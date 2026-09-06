"""Drive a program on a real pty, feeding keystrokes once it has asked for them.

`script` forwards a file to the pty and reaches EOF before the program gets there,
so it can never exercise raw mode. This waits for output to go quiet, then types.
"""
import os, pty, select, sys, time, fcntl, termios, struct

program = sys.argv[1]
script = [
    (b"Ada\r", "a line for the cooked prompt"),
    (b"\x1b[A", "Up arrow      (ESC [ A)"),
    (b"\x1b[6~", "Page Down     (ESC [ 6 ~)"),
    (b"\x01", "Ctrl-A        (0x01)"),
    (b"\x1bOP", "F1            (ESC O P)"),
    (b"\xc3\xa9", "e-acute       (2-byte UTF-8)"),
    (b"\x1b", "bare Escape   (nothing follows)"),
    (b"\x1bx", "Alt-x         (ESC x)"),
    (b"q", "q to finish"),
]

pid, fd = pty.fork()
if pid == 0:
    os.environ["TERM"] = "xterm-256color"
    os.execv(program, [program])

# Give the pty a real size so `Console.size` has something to report.
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 100, 0, 0))

captured = []

def drain(timeout):
    """Read until the program has been quiet for `timeout` seconds."""
    while True:
        ready, _, _ = select.select([fd], [], [], timeout)
        if not ready:
            return
        try:
            chunk = os.read(fd, 65536)
        except OSError:
            return
        if not chunk:
            return
        captured.append(chunk)

for keys, _label in script:
    drain(0.35)
    os.write(fd, keys)
drain(1.0)
os.close(fd)
os.waitpid(pid, 0)
sys.stdout.write(b"".join(captured).decode("utf-8", "replace"))
