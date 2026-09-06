"""Is the terminal still in raw mode after the program dies?

Runs the program on a pty, waits for it to say it has entered raw mode, optionally
sends a signal, then reads the pty's termios back and reports ECHO and ICANON.
"""
import os, pty, select, signal, sys, termios, time

program, action = sys.argv[1], sys.argv[2]

pid, fd = pty.fork()
if pid == 0:
    os.environ["TERM"] = "xterm-256color"
    os.execv(program, [program])

def flags():
    mode = termios.tcgetattr(fd)
    lflag = mode[3]
    return ("ECHO on" if lflag & termios.ECHO else "ECHO OFF",
            "ICANON on" if lflag & termios.ICANON else "ICANON OFF")

# Wait until the child reports it is in raw mode.
seen = b""
deadline = time.time() + 5
while b"raw" not in seen and time.time() < deadline:
    ready, _, _ = select.select([fd], [], [], 0.2)
    if ready:
        try:
            seen += os.read(fd, 4096)
        except OSError:
            break
print(f"  while running: {flags()}")

if action == "signal":
    os.kill(pid, signal.SIGINT)

_, status = os.waitpid(pid, 0)
if os.WIFSIGNALED(status):
    print(f"  exited on signal {os.WTERMSIG(status)}")
else:
    print(f"  exited with status {os.WEXITSTATUS(status)}")
print(f"  after exit:    {flags()}")
os.close(fd)
