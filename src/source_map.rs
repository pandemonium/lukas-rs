//! A tiny registry that lets a [`ParseInfo`](crate::parser::ParseInfo) name the
//! file it came from without carrying a (non-`Copy`) `PathBuf` on every AST node.
//!
//! Each parsed module registers its source path once and gets back a [`FileId`]:
//! a `Copy`, pointer-sized handle that rides along in `ParseInfo`. Errors surfaced
//! after all modules are merged (name/type errors) can then resolve the id back to
//! a path via [`path_of`]. The map is thread-local: parsing and error reporting run
//! on the same thread in the compiler, and each test thread gets its own map.

use std::{cell::RefCell, path::Path, path::PathBuf};

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
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
