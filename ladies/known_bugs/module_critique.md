# Modules: how they actually work, and a critique

Investigation of Marmelade's module system as implemented in `src/ast/namer.rs`
(name resolution) and `src/compiler.rs` (module loading). This is a *design*
critique, not a single failing test — but see `use_local_module/`,
`qualified_ctor_pattern/`, and `brace_on_last_line/` for concrete symptoms.

## How they actually work

Modules are **not** first-class and are **not** a separate namespace. They are a
compile-time naming layer over `IdentifierPath` string prefixes, held in the
`SymbolTable` (namer.rs:560) as:

- `module_members : IdentifierPath -> Vec<ModuleMember>` — what each module path contains,
- `member_modules : ModuleMember -> Vec<IdentifierPath>` — which module paths contain a member,
- `imports : Vec<IdentifierPath>` — a single flat list of opened prefixes,
- `symbols : HashMap<SymbolName, Symbol>` — the one global symbol table (`// Why only one table?`, namer.rs:565).

Declaring `module M:` under `P` (namer.rs:776) does two things:

1. registers `M` as a **term member** of `P` — the code comment is explicit:
   `// Modules compete in the term namespace` (namer.rs:782);
2. recurses into M's contents with the extended path `P.M`, so members are named
   `P.M.member`.

`use` (namer.rs:885) is `add_import_prefix(P.M)` (open) **plus**
`add_module_declaration(... module ...)`, and a `use`d module is always
`External`, i.e. **read from a file** (`load_module_declarations` → `get_source_path`,
compiler.rs:162). So `use` = C `#include` + F# `open` fused.

Resolution of a name `id` (`resolve_free_term_name`, namer.rs:597):

1. `search_space = member_modules[Term(id.head)]` — candidate modules holding the
   *first* segment;
2. `search_order = prefix_chain(current_scope) ++ imports.reverse()` — lexical
   parents first, then every import, last-registered-first (namer.rs:608);
3. take the first module in that order that contains the head; the **leftover path
   segments become `projections`** (namer.rs:629) — the very same `NameExpr`
   representation used for record field access.

## Critique

1. **One namespace for everything.** Modules, values, constructors, *and* witnesses
   all register as term members (namer.rs:764, 740, 783, 838 — "compete in the term
   namespace"). A module and a value with the same name silently coexist:
   `thing := 5` next to `module thing:` gives `thing == 5` **and** `thing.inner == 9`
   (verified). The name means a value or a module depending only on whether a dot
   follows it. No collision is reported.

2. **Qualified access is just record projection.** `M.f` and `record.field` share one
   resolution path and one representation; the split between "module path" and "field
   projection" is decided by string-prefix-matching the dotted path against the set of
   registered module paths (namer.rs:623-631). Modules aren't a distinct semantic
   category — they're "a thing you can dot into," and where the module part ends and
   projection begins is a matter of which prefixes happen to be modules. Brittle and
   inherently ambiguous.

3. **`use` conflates include and open, with no way to separate them.** Always loads a
   file, always opens into unqualified scope. The one field that could separate them —
   `UseDeclaration.qualified_binder` (a `use … as Q` form) — is never produced by the
   parser (only `None`, parser.rs:596) and `todo!()`s in the namer (namer.rs:887).
   Consequences: you cannot open a *local* module at all (`use_local_module`), cannot
   import-without-opening, and every `use` re-reads and re-parses a whole file.

4. **Imports are global and unscoped.** `imports` is a single flat `Vec` on the whole
   symbol table; `add_import_prefix` just appends (namer.rs:896), with no scope key.
   An import written inside one module is not confined to it — semantically every
   `use` is file-global. (Compounded by #3: local modules can't be opened anyway.)

5. **Ambiguity is silent first-match, never reported.** `member_modules` maps a name to
   a *Vec* of modules and resolution takes the first in search order (namer.rs:611).
   Two sources of the same name shadow silently — e.g. a local `map` silently overrides
   the always-open `stdlib.map` with no warning (verified). Real module systems raise
   an "ambiguous reference" error here.

6. **Second-class, no abstraction.** There are no module types/signatures, no sealing or
   interfaces, no functors, no `module M = N` aliasing, and no selective import or
   hiding (`use M (a, b)`, `hiding (…)`). Modules can't be passed, returned, or
   abstracted over. They are purely namespaces — and even that single job is undermined
   by sharing the term namespace (#1) and by qualified access being projection (#2).

7. **Stringly-typed representation.** Everything hangs off `IdentifierPath` string
   prefixes, multi-valued `Vec` maps searched linearly per lookup, and `fresh_name`
   hashing (witnesses are keyed by a hash of their type-signature *string*, namer.rs:834).
   The author's own comments (`// Why only one table?`, `// Modules compete in the term
   namespace`) read as misgivings. It works for small programs but doesn't scale as a
   design.

## What actually needs fixing (and what doesn't)

An earlier draft of this doc recommended giving modules their own (third) namespace.
On reflection that's the wrong lever, and the two-namespace design (values + types,
with modules living among values) is defensible. The problems above are *not* caused by
the namespace count — you can add a third namespace and keep every one of them, or fix
them all while staying at two. The real levers are:

1. **Disambiguate `.` lexically, not by prefix-matching.** The hard question is only
   ever "is `a.b` module-descent or record projection?" A third namespace is one way to
   answer it (look up the head). The cheaper way, which needs no new namespace, is a
   lexical convention — **module names are Capitalized** (as ML/OCaml/Haskell do), so
   `Upper.x` is qualified access and `lower.x` is projection, decided by the shape of the
   head. Marmelade already splits its lexicon this way (constructors/types capitalized,
   values lowercase) — but the module code *breaks its own convention* by accepting
   `module thing:` (lowercase), which is exactly what lets the value `thing` and the
   module `thing` collide (#1) and forces the brittle prefix-matching (#2). Enforce
   capitalization and both problems go away with zero new machinery.

2. **Report ambiguous unqualified references** instead of silently taking the first
   match (#5). This is independent of namespaces — it's just refusing to guess.

3. **Split what `use` welds together** (#3) into three separate operations:
   - **loading** a compilation unit (a file) — once, cached, independent of names;
   - **binding** a module for qualified access so `M.f` works;
   - **opening** a module into unqualified scope, lexically scoped, and applicable to
     *any* module including local `module M:` blocks — not just files.

All three leave the language at **two** namespaces.

### The one honest argument for a third namespace

The real prize of a separate module namespace is the **type + companion-module**
pattern: a type `Stack` *and* a module `Stack` of operations on it, sharing a name.
F#'s confusing errors here are mostly downstream of its `ModuleSuffix` hack — an
auto-rename that exists *because* F# lacks a clean module namespace — so that pain is
evidence for a clean separation, not against it.

But that prize is small in *this* language. The companion-module-of-operations role is
already filled by `signature`/`witness` (a dictionary of operations on a type). If
that's where a type's operations live, you rarely want a `Stack` module beside a `Stack`
type, so the main thing a third namespace would buy, Marmelade mostly doesn't need.
Net: staying at two namespaces is the right call; fix the `.`-disambiguation, the silent
shadowing, and the `use` conflation instead.
