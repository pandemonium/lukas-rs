// Companion implementation of Stdlib.Console.Terminal's `foreign` primitives: terminal
// mode, unbuffered input, and the two queries (is-it-a-tty, how-big-is-it) that the
// styling and editing layers need in order to do the right thing by default.
//
// Everything above these primitives -- SGR rendering, escape-sequence decoding, the
// `in_raw_mode` bracket -- is written in Marmelade. What lives here is exactly the set
// of things that cannot be: termios, poll/read on a bare descriptor, and the process
// teardown paths that have to put the terminal back.
#include <errno.h>
#include <poll.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>

#include "gc.h"

#define CONSOLE_IN  STDIN_FILENO
#define CONSOLE_OUT STDOUT_FILENO

// What `raw_read_byte` returns when it did not return a byte. ABOVE the byte range
// rather than below zero, so the Marmelade side can tell them apart with a plain
// literal pattern -- `deconstruct code into 256 -> ...` -- where a negative sentinel
// would need an if-chain (a negative literal is not currently valid pattern syntax).
// Kept in step with `Console.classify`.
#define CONSOLE_ENDED     256
#define CONSOLE_TIMED_OUT 257
#define CONSOLE_FAILED    258

// ------------------------------------------------------------------ terminal mode
//
// `in_raw_mode` nests, so the saved termios is a STACK, not a single slot: an inner
// bracket that leaves must restore what the outer one installed, not what the shell
// had. Depth is small and bounded -- nesting deeper than this is a program bug, not a
// use case -- so a fixed array avoids an allocation on a path that must also be
// callable from a signal handler.
#define RAW_MAX_DEPTH 16
static struct termios raw_saved[RAW_MAX_DEPTH];
// The mode each level installed: 0 cbreak, 1 full raw. The interpreter needs to know
// which, because full raw turns OPOST off and a line feed then stops returning the
// carriage -- see `raw_mode_current`.
static int raw_modes[RAW_MAX_DEPTH];
static int raw_depth = 0;

// Raw mode is process-wide state that OUTLIVES a crash: a program that aborts with
// ECHO off leaves the user typing blind into their shell. The Marmelade-level bracket
// cannot cover that, because there is no exception to unwind and `omg_wtf_bbq` calls
// `abort` -- so the restore is also hung off `atexit` and off the fatal signals.
static bool exit_hook_installed = false;
static bool signals_installed = false;

// The signals that end a process while the terminal is still raw. SIGABRT is the one
// that matters most and the one an `atexit` hook does NOT cover: `abort()` raises it,
// `omg_wtf_bbq` calls `abort()`, and a raised signal does not run exit handlers -- so
// without this entry a failed assertion left the user typing blind. The rest are here
// for the same reason: whatever kills the program, the terminal goes back first.
static const int fatal_signals[] = {
    SIGINT, SIGTERM, SIGHUP, SIGQUIT, SIGABRT, SIGSEGV, SIGBUS, SIGILL, SIGFPE,
};
#define FATAL_SIGNAL_COUNT ((int)(sizeof fatal_signals / sizeof fatal_signals[0]))
static struct sigaction old_signals[FATAL_SIGNAL_COUNT];

// Async-signal-safe: `tcsetattr`, `signal` and `raise` are all on the POSIX list.
static void console_restore_all(void) {
    if (raw_depth > 0) {
        tcsetattr(CONSOLE_IN, TCSAFLUSH, &raw_saved[0]);
        raw_depth = 0;
    }
}

static void console_on_exit(void) { console_restore_all(); }

// Put the terminal back, then die the way the signal says to -- so the exit status
// still reports "killed by SIGINT" rather than a normal return, and so a crash still
// produces the core dump and still stops in a debugger: the signal is re-delivered with
// its DEFAULT disposition, which is exactly what would have happened without this hook.
static void console_on_signal(int sig) {
    console_restore_all();
    signal(sig, SIG_DFL);
    raise(sig);
}

// Only claim a signal the program has not already claimed. A stdlib that stomped a
// user's SIGINT handler would be trading one wedged terminal for a broken program;
// the disposition is put back on the outermost leave.
static void adopt_signal(int sig, struct sigaction *saved) {
    struct sigaction current;
    if (sigaction(sig, NULL, &current) != 0) return;
    if (current.sa_handler != SIG_DFL) {
        *saved = current;
        return;
    }
    struct sigaction next;
    memset(&next, 0, sizeof next);
    next.sa_handler = console_on_signal;
    sigemptyset(&next.sa_mask);
    sigaction(sig, &next, saved);
}

// raw_mode_enter : Int -> Int
//
// `mode` 0 is cbreak: echo and line assembly off, everything else left alone, so ^C
// still interrupts and ^Z still suspends. `mode` 1 is full raw: the terminal stops
// interpreting anything, so ^C arrives as the byte 0x03 and `\n` no longer implies a
// carriage return on output.
//
// Returns the new nesting depth, or -1 when there is no terminal to put into raw mode
// (a pipe, a file, a CI log). -1 is NOT an error: the caller runs the body anyway and
// skips the matching leave. Reading a pipe byte-at-a-time already behaves the way raw
// mode exists to arrange, and there is no echo to switch off.
FOREIGN_DECL(int64_t, Root_Stdlib_Console_Terminal_raw_mode_enter, int64_t, mode, {
    if (!isatty(CONSOLE_IN)) return -1;
    if (raw_depth >= RAW_MAX_DEPTH) return -1;

    struct termios now;
    if (tcgetattr(CONSOLE_IN, &now) != 0) return -1;

    struct termios next = now;
    // ECHO: stop the driver painting input. ICANON: deliver bytes as they arrive
    // instead of at the newline. IEXTEN: ^V should be a byte, not a quote prefix.
    next.c_lflag &= ~(tcflag_t)(ECHO | ICANON | IEXTEN);
    // ICRNL is the reason Enter would otherwise arrive as 0x0A: the decoder wants to
    // see the key that was actually pressed.
    next.c_iflag &= ~(tcflag_t)ICRNL;
    next.c_cc[VMIN] = 1;
    next.c_cc[VTIME] = 0;

    if (mode != 0) {
        next.c_lflag &= ~(tcflag_t)ISIG;                          // ^C ^Z ^\ become bytes
        next.c_iflag &= ~(tcflag_t)(IXON | BRKINT | INPCK | ISTRIP); // ^S ^Q become bytes
        next.c_oflag &= ~(tcflag_t)OPOST;                         // no \n -> \r\n on the way out
    }

    // TCSAFLUSH, not TCSANOW: discard anything typed ahead, so keystrokes meant for
    // the previous mode are not re-interpreted under the new one.
    if (tcsetattr(CONSOLE_IN, TCSAFLUSH, &next) != 0) return -1;

    raw_saved[raw_depth] = now;
    raw_modes[raw_depth] = (mode != 0);
    raw_depth++;

    if (!exit_hook_installed) {
        atexit(console_on_exit);
        exit_hook_installed = true;
    }
    if (!signals_installed) {
        for (int i = 0; i < FATAL_SIGNAL_COUNT; i++) {
            adopt_signal(fatal_signals[i], &old_signals[i]);
        }
        signals_installed = true;
    }
    return (int64_t)raw_depth;
})

// raw_mode_leave : Unit -> Unit
FOREIGN_DECL(Value, Root_Stdlib_Console_Terminal_raw_mode_leave, Value, ignored, {
    (void)ignored;
    if (raw_depth <= 0) return VUnit();
    raw_depth--;
    tcsetattr(CONSOLE_IN, TCSAFLUSH, &raw_saved[raw_depth]);
    if (raw_depth == 0 && signals_installed) {
        for (int i = 0; i < FATAL_SIGNAL_COUNT; i++) {
            sigaction(fatal_signals[i], &old_signals[i], NULL);
        }
        signals_installed = false;
    }
    return VUnit();
})

// raw_mode_current : Unit -> Int
// -1 not in raw mode, 0 cbreak, 1 full raw. The mode in force, not the nesting depth:
// an inner cbreak inside an outer full raw is cbreak until it leaves.
FOREIGN_DECL(int64_t, Root_Stdlib_Console_Terminal_raw_mode_current, Value, ignored, {
    (void)ignored;
    return raw_depth == 0 ? (int64_t)-1 : (int64_t)raw_modes[raw_depth - 1];
})

// raw_is_output_tty : Unit -> Bool   (is standard OUTPUT a terminal at all)
FOREIGN_DECL(Bool, Root_Stdlib_Console_Terminal_raw_is_output_tty, Value, ignored, {
    (void)ignored;
    return isatty(CONSOLE_OUT) != 0;
})

// ------------------------------------------------------------------------- input
//
// Input goes through `read(2)` on the descriptor, never through `stdin`. Two reasons,
// and the first is fatal on its own: with stdio in the way, `poll` reports "nothing to
// read" while bytes sit in the FILE's buffer, so every timed read -- the one that tells
// a bare Escape from the start of an arrow-key sequence -- would be wrong. The second
// is that stdio's own buffering mode is a process-wide setting this module has no
// business changing under a program that may also be using it.
//
// The refill buffer is static and single-threaded on purpose: a terminal has one
// reader. Two threads racing on stdin would interleave escape sequences and produce
// nonsense whatever this code did.
static uint8_t in_buf[4096];
static size_t in_have = 0;
static size_t in_next = 0;
static bool in_eof = false;

// 1 = a byte is buffered, 0 = timed out, -1 = end of input, -2 = error.
// `timeout_ms` below zero blocks indefinitely.
static int console_fill(int64_t timeout_ms) {
    if (in_next < in_have) return 1;
    if (in_eof) return -1;

    for (;;) {
        struct pollfd waiting = {.fd = CONSOLE_IN, .events = POLLIN, .revents = 0};

        // A blocking wait is exactly the hazard `enter_blocking_call` exists for: this
        // thread is registered with the collector, and a thread asleep in `poll` can
        // never reach a poll point, so every collection would wait for a keystroke.
        enter_blocking_call();
        int ready = poll(&waiting, 1, timeout_ms < 0 ? -1 : (int)timeout_ms);
        int poll_errno = errno;
        leave_blocking_call();

        if (ready < 0) {
            // A signal cut the wait short. Retrying restarts the full timeout rather
            // than the remainder -- acceptable here, where the timeout only ever
            // separates "a lone Escape" from "an escape sequence".
            if (poll_errno == EINTR) continue;
            return -2;
        }
        if (ready == 0) return 0;

        ssize_t got = read(CONSOLE_IN, in_buf, sizeof in_buf);
        if (got < 0) {
            if (errno == EINTR) continue;
            return -2;
        }
        if (got == 0) {
            in_eof = true;
            return -1;
        }
        in_next = 0;
        in_have = (size_t)got;
        return 1;
    }
}

// raw_read_byte : Int -> Int
// The byte 0..255, or one of the CONSOLE_* statuses above. The three non-byte outcomes
// are distinguished rather than collapsed because the decoder genuinely needs to tell
// "nothing came in 25ms" (a bare Escape) from "the terminal closed".
FOREIGN_DECL(int64_t, Root_Stdlib_Console_Terminal_raw_read_byte, int64_t, timeout_ms, {
    switch (console_fill(timeout_ms)) {
        case 1:  return (int64_t)in_buf[in_next++];
        case 0:  return CONSOLE_TIMED_OUT;
        case -1: return CONSOLE_ENDED;
        default: return CONSOLE_FAILED;
    }
})

// raw_read_line : Unit -> Result Int Bytes
// Reads through the next newline, or to end of input.
//
// `Return bytes` for a line, INCLUDING a last line the input ended without terminating,
// and including an empty one -- `Return ""` is a bare Enter, which the caller must be
// able to tell from a closed pipe. `Fault CONSOLE_ENDED` is that closed pipe: the input
// ended with nothing pending. `Fault CONSOLE_FAILED` is a read error.
//
// The error case is separated from EOF, and a line cut short by an error is NOT handed
// back as though it were complete. It used to be both: `if (status != 1) break` treated
// -2 exactly like -1, so a descriptor that failed three bytes into "hello" returned
// `This "hal"` and the caller had no way to know.
//
// BYTES, not Text: whatever the terminal hands over is bytes, and `Text` carries a
// validated-UTF-8 invariant that nothing here has checked. `Console.read_line` runs
// them through `Text.from_bytes`, which is the only thing entitled to make that claim.
//
// In cooked mode the terminal driver has already done the editing: backspace, ^W, ^U
// and the rest were resolved before these bytes ever became readable. That is the whole
// point of this entry -- it is the plain line reader, not a reimplementation of one.
FOREIGN_DECL(Value, Root_Stdlib_Console_Terminal_raw_read_line, Value, ignored, {
    (void)ignored;
    // Kept across calls: a line reader is called in a loop, and regrowing to the same
    // size on every iteration is pure waste. One reader, so one buffer.
    static char *line = NULL;
    static size_t capacity = 0;
    // Set when a line ended on CR, so the LF that may follow is not read as an empty line.
    static bool skip_leading_lf = false;

    size_t length = 0;
    bool terminated = false;
    bool ended = false;

    for (;;) {
        int status = console_fill(-1);
        if (status == -1) { ended = true; break; }
        if (status != 1) return result_fault(VInt(CONSOLE_FAILED));

        uint8_t byte = in_buf[in_next++];

        // The LF of a CRLF whose CR ended the previous line. Carried in a flag rather
        // than peeked at the time, because the two halves can land in different reads,
        // and because peeking after a lone CR would block for a byte that never comes.
        if (skip_leading_lf) {
            skip_leading_lf = false;
            if (byte == '\n') continue;
        }

        // EITHER terminator ends the line. This is what lets `read_line` work in raw
        // mode: with ICRNL cleared, Return delivers CR and never LF, so a reader that
        // waits for LF alone would hang forever -- a restriction that was mine, not the
        // terminal's, and one no caller should have to remember.
        if (byte == '\n') {
            terminated = true;
            break;
        }
        if (byte == '\r') {
            terminated = true;
            skip_leading_lf = true;
            break;
        }
        if (length == capacity) {
            size_t grown = capacity == 0 ? 128 : capacity * 2;
            char *bigger = realloc(line, grown);
            // Out of memory is a failure to read the line, not the end of the input.
            if (bigger == NULL) return result_fault(VInt(CONSOLE_FAILED));
            line = bigger;
            capacity = grown;
        }
        line[length++] = (char)byte;
    }

    if (ended && length == 0 && !terminated) return result_fault(VInt(CONSOLE_ENDED));
    return result_return(mk_textn(line, length));
})

// ------------------------------------------------------------------------ output
// Output DOES go through stdio, unlike input: nothing here depends on knowing when a
// byte reaches the terminal except the explicit flush, and sharing the buffer with
// `print_endline` keeps the two from interleaving out of order.

// raw_write : Text -> Unit
FOREIGN_DECL(Value, Root_Stdlib_Console_Terminal_raw_write, Value, text, {
    // Text is an OBJ_SLICE carrying an explicit length and no NUL; write its bytes.
    fwrite(slice_ptr(text), 1, slice_len(text), stdout);
    return VUnit();
})

// raw_flush : Unit -> Unit
FOREIGN_DECL(Value, Root_Stdlib_Console_Terminal_raw_flush, Value, ignored, {
    (void)ignored;
    fflush(stdout);
    return VUnit();
})

// ------------------------------------------------------------------------ queries

// raw_is_tty : Unit -> Bool   (is INPUT a terminal -- the question raw mode turns on)
FOREIGN_DECL(Bool, Root_Stdlib_Console_Terminal_raw_is_tty, Value, ignored, {
    (void)ignored;
    return isatty(CONSOLE_IN) != 0;
})

// raw_supports_colour : Unit -> Bool
// Asks about OUTPUT, and answers the three questions every well-behaved program is
// expected to ask: is this a terminal at all, has the user opted out via NO_COLOR
// (no-color.org: set and non-empty), and does TERM admit to understanding anything.
FOREIGN_DECL(Bool, Root_Stdlib_Console_Terminal_raw_supports_colour, Value, ignored, {
    (void)ignored;
    if (!isatty(CONSOLE_OUT)) return false;

    const char *opted_out = getenv("NO_COLOR");
    if (opted_out != NULL && opted_out[0] != '\0') return false;

    const char *term = getenv("TERM");
    if (term == NULL || strcmp(term, "dumb") == 0) return false;

    return true;
})

// raw_window_size : Unit -> Perhaps (Int, Int)   (columns, rows)
FOREIGN_DECL(Value, Root_Stdlib_Console_Terminal_raw_window_size, Value, ignored, {
    (void)ignored;
    struct winsize size;
    if (ioctl(CONSOLE_OUT, TIOCGWINSZ, &size) != 0 || size.ws_col == 0) {
        return perhaps_nope();
    }
    return perhaps_this(mk_tuple2(VInt(size.ws_col), VInt(size.ws_row)));
})
