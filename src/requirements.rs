use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt, fs, io,
    path::{Path, PathBuf},
};

use crate::{
    ast::namer::{QualifiedName, SymbolName},
    parser::{Identifier, IdentifierPath},
    phase,
    typer::Types,
};

/// A terminal root in the build-requirement graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Platform {
    NativeMacOS,
    NativeLinux,
    NativeWindows,
    WasmNode,
    WasmBrowser,
}

impl Platform {
    #[cfg(target_os = "macos")]
    pub const fn current_native() -> Self {
        Self::NativeMacOS
    }

    #[cfg(target_os = "linux")]
    pub const fn current_native() -> Self {
        Self::NativeLinux
    }

    #[cfg(target_os = "windows")]
    pub const fn current_native() -> Self {
        Self::NativeWindows
    }

    pub const fn requirement_name(self) -> &'static str {
        match self {
            Self::NativeMacOS => "Native_MacOS",
            Self::NativeLinux => "Native_Linux",
            Self::NativeWindows => "Native_Windows",
            Self::WasmNode => "Wasm_Node",
            Self::WasmBrowser => "Wasm_Browser",
        }
    }
}

impl fmt::Display for Platform {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.requirement_name())
    }
}

/// One alternative implementation of a capability. Providers are OR choices;
/// every requirement within one provider is an AND obligation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Provider {
    pub name: String,
    pub provides: String,
    pub requires: Vec<String>,
    pub defines: Vec<String>,
    pub sources: Vec<PathBuf>,
}

/// The build-supplied information model. Capability names describe consumer
/// requirements, roots describe terminal platforms, and providers connect them.
#[derive(Clone, Debug)]
pub struct CapabilityModel {
    roots: HashSet<String>,
    capabilities: HashSet<String>,
    providers: Vec<Provider>,
}

#[derive(Debug)]
pub struct ModelError {
    pub line: Option<usize>,
    pub message: String,
}

impl fmt::Display for ModelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.line {
            Some(line) => write!(f, "line {line}: {}", self.message),
            None => f.write_str(&self.message),
        }
    }
}

impl std::error::Error for ModelError {}

impl From<io::Error> for ModelError {
    fn from(error: io::Error) -> Self {
        Self {
            line: None,
            message: error.to_string(),
        }
    }
}

impl CapabilityModel {
    /// Read the deliberately small, dependency-free build-model format:
    ///
    /// ```text
    /// root Wasm_Browser
    /// capability Timer
    /// provider Browser_Timer provides Timer requires Wasm_Browser defines MARM_TIMER_BROWSER
    /// ```
    ///
    /// `requires`, `defines`, and `sources` accept comma-separated values. Paths
    /// are resolved relative to the model file. Provider order is preference order.
    pub fn load(path: &Path) -> Result<Self, ModelError> {
        let source = fs::read_to_string(path)?;
        Self::parse(&source, path.parent().unwrap_or_else(|| Path::new(".")))
    }

    pub fn parse(source: &str, base: &Path) -> Result<Self, ModelError> {
        let mut roots = HashSet::new();
        let mut capabilities = HashSet::new();
        let mut providers = Vec::new();
        let mut provider_names = HashSet::new();

        for (line_index, original) in source.lines().enumerate() {
            let line_number = line_index + 1;
            let line = original.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            let words = line.split_whitespace().collect::<Vec<_>>();
            let fail = |message: String| ModelError {
                line: Some(line_number),
                message,
            };
            match words.as_slice() {
                ["root", name] => {
                    valid_name(name)
                        .then_some(())
                        .ok_or_else(|| fail(format!("invalid platform-root name `{name}`")))?;
                    if !roots.insert((*name).to_owned()) {
                        return Err(fail(format!("duplicate platform root `{name}`")));
                    }
                }
                ["capability", name] => {
                    valid_name(name)
                        .then_some(())
                        .ok_or_else(|| fail(format!("invalid capability name `{name}`")))?;
                    if !capabilities.insert((*name).to_owned()) {
                        return Err(fail(format!("duplicate capability `{name}`")));
                    }
                }
                ["provider", name, rest @ ..] => {
                    valid_name(name)
                        .then_some(())
                        .ok_or_else(|| fail(format!("invalid provider name `{name}`")))?;
                    if !provider_names.insert((*name).to_owned()) {
                        return Err(fail(format!("duplicate provider `{name}`")));
                    }
                    let mut fields = HashMap::<&str, &str>::new();
                    let mut cursor = 0;
                    while cursor < rest.len() {
                        let key = rest[cursor];
                        let Some(value) = rest.get(cursor + 1) else {
                            return Err(fail(format!("provider field `{key}` has no value")));
                        };
                        if !matches!(key, "provides" | "requires" | "defines" | "sources") {
                            return Err(fail(format!("unknown provider field `{key}`")));
                        }
                        if fields.insert(key, value).is_some() {
                            return Err(fail(format!("duplicate provider field `{key}`")));
                        }
                        cursor += 2;
                    }
                    let provides = fields
                        .remove("provides")
                        .ok_or_else(|| fail("provider is missing `provides`".to_owned()))?;
                    let requires = fields
                        .remove("requires")
                        .ok_or_else(|| fail("provider is missing `requires`".to_owned()))?;
                    let requires = comma_values(requires, "requires", line_number)?;
                    let defines = fields
                        .remove("defines")
                        .map(|value| comma_values(value, "defines", line_number))
                        .transpose()?
                        .unwrap_or_default();
                    for define in &defines {
                        if !valid_c_identifier(define) {
                            return Err(fail(format!("invalid C preprocessor name `{define}`")));
                        }
                    }
                    let sources = fields
                        .remove("sources")
                        .map(|value| comma_values(value, "sources", line_number))
                        .transpose()?
                        .unwrap_or_default()
                        .into_iter()
                        .map(|source| base.join(source))
                        .collect();
                    providers.push(Provider {
                        name: (*name).to_owned(),
                        provides: provides.to_owned(),
                        requires,
                        defines,
                        sources,
                    });
                }
                _ => {
                    return Err(fail(
                        "expected `root`, `capability`, or `provider` declaration".to_owned(),
                    ));
                }
            }
        }

        for provider in &providers {
            if !capabilities.contains(&provider.provides) {
                return Err(ModelError {
                    line: None,
                    message: format!(
                        "provider `{}` provides undeclared capability `{}`",
                        provider.name, provider.provides
                    ),
                });
            }
            for requirement in &provider.requires {
                if !capabilities.contains(requirement) && !roots.contains(requirement) {
                    return Err(ModelError {
                        line: None,
                        message: format!(
                            "provider `{}` requires undeclared node `{requirement}`",
                            provider.name
                        ),
                    });
                }
            }
        }

        Ok(Self {
            roots,
            capabilities,
            providers,
        })
    }

    pub fn resolve(
        &self,
        requirements: impl IntoIterator<Item = IdentifierPath>,
        platform: Platform,
    ) -> Resolution {
        let target = platform.requirement_name();
        let mut managed_sources = self
            .providers
            .iter()
            .flat_map(|provider| provider.sources.iter().cloned())
            .collect::<Vec<_>>();
        managed_sources.sort();
        managed_sources.dedup();
        let mut selected = Vec::new();
        let mut selected_names = HashSet::new();
        let mut unsatisfied = Vec::new();

        if !self.roots.contains(target) {
            unsatisfied.push(format!("target root `{target}` is not declared"));
            return Resolution {
                platform,
                providers: selected,
                managed_sources,
                unsatisfied,
            };
        }

        let mut names = requirements
            .into_iter()
            .map(|requirement| requirement.to_string())
            .collect::<Vec<_>>();
        names.sort();
        names.dedup();
        for name in names {
            if !self.capabilities.contains(&name) {
                unsatisfied.push(format!("`{name}` is not a declared capability"));
                continue;
            }
            let mut active = HashSet::new();
            if let Some(indices) = self.resolve_node(&name, target, &mut active) {
                for index in indices {
                    let provider = self.providers[index].clone();
                    if selected_names.insert(provider.name.clone()) {
                        selected.push(provider);
                    }
                }
            } else {
                unsatisfied.push(format!("`{name}` has no provider reaching `{target}`"));
            }
        }

        Resolution {
            platform,
            providers: selected,
            managed_sources,
            unsatisfied,
        }
    }

    fn resolve_node(
        &self,
        name: &str,
        target: &str,
        active: &mut HashSet<String>,
    ) -> Option<Vec<usize>> {
        if name == target {
            return Some(Vec::new());
        }
        if !active.insert(name.to_owned()) {
            return None;
        }
        for (index, provider) in self.providers.iter().enumerate() {
            if provider.provides != name {
                continue;
            }
            let mut chosen = vec![index];
            let mut works = true;
            for requirement in &provider.requires {
                let Some(mut dependencies) = self.resolve_node(requirement, target, active) else {
                    works = false;
                    break;
                };
                chosen.append(&mut dependencies);
            }
            if works {
                active.remove(name);
                return Some(chosen);
            }
        }
        active.remove(name);
        None
    }
}

fn comma_values(value: &str, field: &str, line: usize) -> Result<Vec<String>, ModelError> {
    let values = value.split(',').map(str::trim).collect::<Vec<_>>();
    if values.is_empty() || values.iter().any(|value| value.is_empty()) {
        return Err(ModelError {
            line: Some(line),
            message: format!("provider field `{field}` contains an empty value"),
        });
    }
    Ok(values.into_iter().map(str::to_owned).collect())
}

fn valid_name(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '-'))
}

fn valid_c_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

#[derive(Clone, Debug)]
pub struct Resolution {
    pub platform: Platform,
    pub providers: Vec<Provider>,
    /// Every source owned by any provider in the model. The generic C source
    /// scan must omit these and then add back only sources of selected providers.
    pub managed_sources: Vec<PathBuf>,
    pub unsatisfied: Vec<String>,
}

impl Resolution {
    pub fn is_satisfied(&self) -> bool {
        self.unsatisfied.is_empty()
    }

    pub fn write_plan(&self, path: &Path) -> io::Result<()> {
        let mut plan = format!("target {}\n", self.platform);
        for source in &self.managed_sources {
            plan.push_str(&format!("managed-source {}\n", source.display()));
        }
        for provider in &self.providers {
            plan.push_str(&format!("provider {}\n", provider.name));
            for define in &provider.defines {
                plan.push_str(&format!("define {define}\n"));
            }
            for source in &provider.sources {
                plan.push_str(&format!("source {}\n", source.display()));
            }
        }
        fs::write(path, plan)
    }
}

#[derive(Clone, Debug)]
pub struct RequirementTrace {
    pub requirement: IdentifierPath,
    pub path: Vec<SymbolName>,
}

#[derive(Clone, Debug)]
pub struct RequirementAnalysis {
    pub summaries: HashMap<SymbolName, HashSet<IdentifierPath>>,
    pub entry_traces: Vec<RequirementTrace>,
}

impl RequirementAnalysis {
    pub fn write_report(&self, path: &Path) -> io::Result<()> {
        let mut rows = self
            .summaries
            .iter()
            .filter(|(_, requirements)| !requirements.is_empty())
            .map(|(symbol, requirements)| {
                let mut requirements = requirements
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>();
                requirements.sort();
                format!("{symbol}: {}", requirements.join(", "))
            })
            .collect::<Vec<_>>();
        rows.sort();
        fs::write(
            path,
            rows.join("\n") + if rows.is_empty() { "" } else { "\n" },
        )
    }
}

/// Infer and retain the requirement summary for every symbol. This is a monotone
/// fixed point over the ordinary dependency graph, so recursive groups converge.
/// The entry traces are a separate breadth-first walk for useful diagnostics.
pub fn infer(symbols: &phase::SymbolTable<Types>, entry: QualifiedName) -> RequirementAnalysis {
    let graph = symbols
        .dependency_matrix()
        .edges()
        .map(|(symbol, dependencies)| (symbol.clone(), dependencies.to_vec()))
        .collect::<HashMap<_, _>>();
    let foreign = symbols
        .foreign_terms
        .iter()
        .map(|term| (SymbolName::Term(term.name.clone()), term))
        .collect::<HashMap<_, _>>();

    let mut summaries = HashMap::<SymbolName, HashSet<IdentifierPath>>::new();
    for symbol in graph.keys().chain(foreign.keys()) {
        summaries.entry(symbol.clone()).or_default();
    }
    for (symbol, term) in &foreign {
        summaries.entry(symbol.clone()).or_default().extend(
            term.requirements
                .iter()
                .map(|requirement| requirement.name.clone()),
        );
    }
    loop {
        let previous = summaries.clone();
        let mut changed = false;
        for (symbol, dependencies) in &graph {
            let inherited = dependencies
                .iter()
                .flat_map(|dependency| previous.get(dependency).into_iter().flatten().cloned())
                .collect::<Vec<_>>();
            let summary = summaries.entry(symbol.clone()).or_default();
            let old_len = summary.len();
            summary.extend(inherited);
            changed |= summary.len() != old_len;
        }
        if !changed {
            break;
        }
    }

    let entry = SymbolName::Term(entry);
    let mut queue = VecDeque::from([(entry.clone(), vec![entry])]);
    let mut visited = HashSet::new();
    let mut found = HashMap::<IdentifierPath, Vec<SymbolName>>::new();
    while let Some((symbol, path)) = queue.pop_front() {
        if !visited.insert(symbol.clone()) {
            continue;
        }
        if let Some(term) = foreign.get(&symbol) {
            for requirement in &term.requirements {
                found
                    .entry(requirement.name.clone())
                    .or_insert_with(|| path.clone());
            }
        }
        let mut dependencies = graph.get(&symbol).cloned().unwrap_or_default();
        dependencies.sort_by_key(ToString::to_string);
        for dependency in dependencies {
            let mut dependency_path = path.clone();
            dependency_path.push(dependency.clone());
            queue.push_back((dependency, dependency_path));
        }
    }
    let mut entry_traces = found
        .into_iter()
        .map(|(requirement, path)| RequirementTrace { requirement, path })
        .collect::<Vec<_>>();
    entry_traces.sort_by_key(|trace| trace.requirement.to_string());

    RequirementAnalysis {
        summaries,
        entry_traces,
    }
}

pub fn root_entry() -> QualifiedName {
    QualifiedName::from_root_symbol(Identifier::from_str("start"))
}

#[cfg(test)]
mod tests {
    use super::*;

    const MODEL: &str = r#"
root Native_MacOS
root Wasm_Browser
capability Socket
capability Browser
capability Web_Socket
provider Mac_Socket provides Socket requires Native_MacOS defines MARM_SOCKET_POSIX
provider Browser_API provides Browser requires Wasm_Browser
provider Browser_WebSocket provides Web_Socket requires Browser
provider Native_WebSocket provides Web_Socket requires Socket
"#;

    #[test]
    fn alternative_providers_reach_different_roots() {
        let model = CapabilityModel::parse(MODEL, Path::new(".")).unwrap();
        let requirement = IdentifierPath::new("Web_Socket");
        let native = model.resolve([requirement.clone()], Platform::NativeMacOS);
        let browser = model.resolve([requirement], Platform::WasmBrowser);

        assert!(native.is_satisfied());
        assert_eq!(native.providers.last().unwrap().name, "Mac_Socket");
        assert!(browser.is_satisfied());
        assert_eq!(browser.providers.last().unwrap().name, "Browser_API");
    }

    #[test]
    fn undeclared_and_unprovided_requirements_fail() {
        let model = CapabilityModel::parse(MODEL, Path::new(".")).unwrap();
        assert!(
            !model
                .resolve([IdentifierPath::new("Made_Up")], Platform::NativeMacOS)
                .is_satisfied()
        );
        assert!(
            !model
                .resolve([IdentifierPath::new("Browser")], Platform::NativeMacOS)
                .is_satisfied()
        );
    }

    #[test]
    fn malformed_models_are_rejected() {
        let error = CapabilityModel::parse(
            "capability Timer\nprovider Clock provides Timer requires Missing\n",
            Path::new("."),
        )
        .unwrap_err();
        assert!(error.to_string().contains("undeclared node `Missing`"));
    }

    #[test]
    fn provider_build_inputs_are_resolved_relative_to_the_model() {
        let model = CapabilityModel::parse(
            r#"
root Wasm_Browser
root Wasm_Node
capability Dom
provider Dom_JS provides Dom requires Wasm_Browser defines MARM_DOM_JS sources providers/dom.c
provider Dom_Node provides Dom requires Wasm_Node defines MARM_DOM_NODE sources providers/dom-node.c
"#,
            Path::new("/configuration"),
        )
        .unwrap();
        let resolution = model.resolve([IdentifierPath::new("Dom")], Platform::WasmBrowser);

        assert!(resolution.is_satisfied());
        assert_eq!(resolution.providers[0].defines, ["MARM_DOM_JS"]);
        assert_eq!(
            resolution.providers[0].sources,
            [PathBuf::from("/configuration/providers/dom.c")]
        );
        assert_eq!(
            resolution.managed_sources,
            [
                PathBuf::from("/configuration/providers/dom-node.c"),
                PathBuf::from("/configuration/providers/dom.c")
            ]
        );

        let plan =
            std::env::temp_dir().join(format!("lukas-provider-plan-{}.txt", std::process::id()));
        resolution.write_plan(&plan).unwrap();
        let plan = fs::read_to_string(plan).unwrap();
        assert!(plan.contains("managed-source /configuration/providers/dom-node.c"));
        assert!(plan.contains("managed-source /configuration/providers/dom.c"));
        assert!(
            plan.lines()
                .any(|line| line == "source /configuration/providers/dom.c")
        );
        assert!(
            !plan
                .lines()
                .any(|line| line == "source /configuration/providers/dom-node.c")
        );
    }
}
