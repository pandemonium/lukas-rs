//! A tiny registry that lets a [`ParseInfo`](crate::parser::ParseInfo) name the
//! file it came from without carrying a (non-`Copy`) `PathBuf` on every AST node.
//!
//! Each parsed module registers its source path once and gets back a [`FileId`]:
//! a `Copy`, pointer-sized handle that rides along in `ParseInfo`. Errors surfaced
//! after all modules are merged (name/type errors) can then resolve the id back to
//! a path via [`path_of`]. The map is thread-local: parsing and error reporting run
//! on the same thread in the compiler, and each test thread gets its own map.

use std::{cell::RefCell, collections::HashMap, fs, io, path::Path, path::PathBuf};

/// A registered source file: its path plus its lines, kept so errors can quote the
/// offending source rather than a phase-internal expression rendering (e.g. `#3`).
struct Source {
    path: PathBuf,
    lines: Vec<String>,
}

/// A handle identifying a source file in the thread-local [source map](self).
///
/// `FileId::UNKNOWN` (the [`Default`]) marks a `ParseInfo` with no on-disk origin --
/// compiler-synthesised nodes and the always-injected `Prelude` import. Real files
/// get ids counting up from one.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(u32);

impl FileId {
    /// The sentinel for nodes with no source file.
    pub const UNKNOWN: Self = Self(0);
}

impl Default for FileId {
    fn default() -> Self {
        Self::UNKNOWN
    }
}

thread_local! {
    /// Registered sources, indexed by `FileId(n)` at position `n - 1`.
    static SOURCES: RefCell<Vec<Source>> = const { RefCell::new(Vec::new()) };

    /// The file whose tokens are currently being parsed. `ParseInfo::from_position`
    /// stamps freshly-built nodes with this, so no parser call site has to thread it.
    static CURRENT: RefCell<FileId> = const { RefCell::new(FileId::UNKNOWN) };

    /// Editor buffers standing in for what is on disk, keyed by canonical path.
    /// Empty in the compiler; a language server installs the open, unsaved buffers
    /// here for the duration of one check (see [`with_overlay`]) so it checks what
    /// the programmer is looking at rather than what was last saved.
    static OVERLAY: RefCell<HashMap<PathBuf, String>> = RefCell::new(HashMap::new());
}

/// Overlay keys are canonical, so `ladies/stdlib/Foo.lady` reached through a
/// relative `--library` and the absolute path an editor sends are the same key.
/// A path that does not exist yet (a buffer never saved) canonicalises to itself.
fn key(path: &Path) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

/// Read a module's source: the overlaid buffer if one is installed for this path,
/// otherwise the file on disk.
pub fn read(path: &Path) -> io::Result<String> {
    let overlaid = OVERLAY.with_borrow(|overlay| overlay.get(&key(path)).cloned());
    match overlaid {
        Some(text) => Ok(text),
        None => fs::read_to_string(path),
    }
}

/// Install `buffers` as the overlay for the duration of `body`, restoring whatever
/// was there before. Takes a snapshot by value: a server holds the live buffers on
/// its own thread and hands a copy to each check.
pub fn with_overlay<A>(buffers: HashMap<PathBuf, String>, body: impl FnOnce() -> A) -> A {
    let buffers = buffers
        .into_iter()
        .map(|(path, text)| (key(&path), text))
        .collect();
    let previous = OVERLAY.with_borrow_mut(|overlay| std::mem::replace(overlay, buffers));
    let result = body();
    OVERLAY.with_borrow_mut(|overlay| *overlay = previous);
    result
}

/// Forget every registered source. The map only grows, which is right for a compiler
/// that exits after one program and wrong for a server that checks the same files
/// over and over: without this, ids and quoted lines accumulate for the life of the
/// process. Call it before a check, never during one -- live `FileId`s go stale.
pub fn reset() {
    SOURCES.with_borrow_mut(Vec::clear);
    CURRENT.with_borrow_mut(|current| *current = FileId::UNKNOWN);
}

/// Register `path` with its `source` text and return its id. Registering the same
/// path twice yields two ids; that is fine -- ids are for reporting, not identity,
/// and each module is loaded once.
pub fn register(path: &Path, source: &str) -> FileId {
    SOURCES.with_borrow_mut(|sources| {
        sources.push(Source {
            path: path.to_path_buf(),
            lines: source.lines().map(str::to_owned).collect(),
        });
        FileId(sources.len() as u32)
    })
}

/// The path a [`FileId`] was registered with, or `None` for `FileId::UNKNOWN` (or
/// an id from another thread's map).
pub fn path_of(id: FileId) -> Option<PathBuf> {
    let FileId(n) = id;
    if n == 0 {
        return None;
    }
    SOURCES.with_borrow(|sources| sources.get((n - 1) as usize).map(|s| s.path.clone()))
}

/// A two-line source excerpt for a 1-based `row`/`column`: the offending source line
/// and a caret line pointing at the column, indented to align under the header. Used
/// by error rendering so a diagnostic quotes real source rather than a phase-internal
/// term rendering. `None` when the file/line is unknown.
pub fn snippet(id: FileId, row: u32, column: u32) -> Option<String> {
    let FileId(n) = id;
    if n == 0 {
        return None;
    }
    SOURCES.with_borrow(|sources| {
        let line = sources
            .get((n - 1) as usize)?
            .lines
            .get((row as usize).checked_sub(1)?)?;
        // A fixed-width gutter (`  <row> | `) keeps the caret aligned with the quoted
        // line. The caret sits `column - 1` characters into the line's text.
        let gutter = format!("{row:>6} | ");
        let pad = " ".repeat(gutter.len());
        let caret = " ".repeat(column.saturating_sub(1) as usize);
        Some(format!("{gutter}{line}\n{pad}{caret}^"))
    })
}

/// A digest of `file`'s text from `from` up to (not including) `to`, or to the
/// end of the file when `to` is `None`. Positions are 1-based, and a column
/// counts characters.
///
/// This is how a check works out what the programmer changed: the declarations
/// of a file partition it, and a declaration whose text hashes the same as it
/// did last time did not change. Returns `None` for a file the map does not
/// know, which reads as "cannot tell" -- the caller must then assume a change.
pub fn digest_between(
    id: FileId,
    from: crate::lexer::SourceLocation,
    to: Option<crate::lexer::SourceLocation>,
) -> Option<u64> {
    use std::hash::{Hash, Hasher};

    let FileId(n) = id;
    if n == 0 {
        return None;
    }

    SOURCES.with_borrow(|sources| {
        let lines = &sources.get((n - 1) as usize)?.lines;
        let last = to.map_or(lines.len(), |to| (to.row as usize).min(lines.len()));

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        for row in (from.row as usize)..=last {
            let Some(line) = lines.get(row.saturating_sub(1)) else {
                continue;
            };
            // Only the first and last lines of the span are partial.
            let start = (row == from.row as usize).then(|| from.column.saturating_sub(1) as usize);
            let end = to
                .filter(|to| row == to.row as usize)
                .map(|to| to.column.saturating_sub(1) as usize);
            let text = slice_characters(line, start.unwrap_or(0), end);
            text.hash(&mut hasher);
            // A line break is a token here: without it, moving a word from the
            // end of one line to the start of the next would hash the same.
            0u8.hash(&mut hasher);
        }
        Some(hasher.finish())
    })
}

/// `line[from..to]`, counting characters rather than bytes, which is what a
/// `SourceLocation`'s column means.
fn slice_characters(line: &str, from: usize, to: Option<usize>) -> &str {
    let start = line
        .char_indices()
        .nth(from)
        .map_or(line.len(), |(at, _)| at);
    let end = to
        .and_then(|to| line.char_indices().nth(to).map(|(at, _)| at))
        .unwrap_or(line.len())
        .max(start);
    &line[start..end]
}

/// The id stamped onto nodes parsed right now. Read by `ParseInfo::from_position`.
pub fn current() -> FileId {
    CURRENT.with_borrow(|c| *c)
}

/// Make `id` the current file for the duration of `body`, restoring the previous
/// current file afterwards (so nested/sequential module parses don't leak into
/// each other). Returns whatever `body` returns.
pub fn with_current<A>(id: FileId, body: impl FnOnce() -> A) -> A {
    let previous = CURRENT.with_borrow_mut(|c| std::mem::replace(c, id));
    let result = body();
    CURRENT.with_borrow_mut(|c| *c = previous);
    result
}
