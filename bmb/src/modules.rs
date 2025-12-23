//! Module system for BMB
//!
//! Handles module resolution, loading, dependency management, and module indexing.
//!
//! The module system has two main components:
//! 1. **Module Resolution** (@use): Loading external BMB files
//! 2. **Module Index** (@module): Building a queryable index of all modules

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

#[allow(unused_imports)] // Used in tests
use crate::ast::{Identifier, ModuleDecl, ModulePath, ModuleUse, Node, Program};
use crate::{parser, BmbError, Result};

// ========== Module Index System ==========

/// An entry in the module index
#[derive(Debug, Clone)]
pub struct ModuleEntry {
    /// Full module path (e.g., ["math", "arithmetic"])
    pub path: Vec<String>,
    /// The module declaration span
    pub decl_span: crate::ast::Span,
    /// Nodes defined in this module
    pub nodes: Vec<String>,
    /// Tags associated with this module's nodes
    pub tags: HashSet<String>,
    /// Source file path (if known)
    pub source_path: Option<PathBuf>,
}

impl ModuleEntry {
    /// Get the full dotted module path
    pub fn full_path(&self) -> String {
        self.path.join(".")
    }
}

/// A hierarchical tree node for module organization
#[derive(Debug, Clone, Default)]
pub struct ModuleTreeNode {
    /// Name of this tree node
    pub name: String,
    /// Module entry if this is a leaf module
    pub entry: Option<ModuleEntry>,
    /// Child modules
    pub children: HashMap<String, ModuleTreeNode>,
}

impl ModuleTreeNode {
    /// Create a new tree node
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            entry: None,
            children: HashMap::new(),
        }
    }

    /// Insert a module at the given path
    fn insert(&mut self, path: &[String], entry: ModuleEntry) {
        if path.is_empty() {
            self.entry = Some(entry);
            return;
        }

        let first = &path[0];
        let child = self
            .children
            .entry(first.clone())
            .or_insert_with(|| ModuleTreeNode::new(first));
        child.insert(&path[1..], entry);
    }

    /// Get a module at the given path
    fn get(&self, path: &[String]) -> Option<&ModuleEntry> {
        if path.is_empty() {
            return self.entry.as_ref();
        }

        let first = &path[0];
        self.children.get(first).and_then(|c| c.get(&path[1..]))
    }

    /// Get all modules under this node (recursive)
    fn collect_all(&self, prefix: &[String], results: &mut Vec<ModuleEntry>) {
        if let Some(ref entry) = self.entry {
            results.push(entry.clone());
        }

        for (name, child) in &self.children {
            let mut new_prefix = prefix.to_vec();
            new_prefix.push(name.clone());
            child.collect_all(&new_prefix, results);
        }
    }

    /// Get all modules matching a path prefix
    fn get_by_prefix(&self, prefix: &[String]) -> Vec<ModuleEntry> {
        if prefix.is_empty() {
            let mut results = Vec::new();
            self.collect_all(&[], &mut results);
            return results;
        }

        let first = &prefix[0];
        if let Some(child) = self.children.get(first) {
            child.get_by_prefix(&prefix[1..])
        } else {
            Vec::new()
        }
    }
}

/// Module Index for queryable module discovery
///
/// The Index system provides:
/// - Hierarchical module organization via @module declarations
/// - Fast lookup by module path
/// - Tag-based querying for semantic discovery
///
/// # Example
/// ```ignore
/// let mut index = ModuleIndex::new();
/// index.add_from_program(&program, Some("math.bmb"));
///
/// // Query by path
/// if let Some(entry) = index.get("math.arithmetic") {
///     println!("Found module with {} nodes", entry.nodes.len());
/// }
///
/// // Query by tag
/// let pure_modules = index.find_by_tag("pure");
/// ```
#[derive(Debug, Clone, Default)]
pub struct ModuleIndex {
    /// Hierarchical tree of modules
    tree: ModuleTreeNode,
    /// Flat map for fast lookup by full path
    by_path: HashMap<String, ModuleEntry>,
    /// Inverted index: tag -> module paths
    by_tag: HashMap<String, HashSet<String>>,
}

impl ModuleIndex {
    /// Create a new empty module index
    pub fn new() -> Self {
        Self {
            tree: ModuleTreeNode::new("root"),
            by_path: HashMap::new(),
            by_tag: HashMap::new(),
        }
    }

    /// Add a module entry from a parsed program
    ///
    /// If the program has a @module declaration, it will be indexed.
    /// Otherwise, the source path (if provided) will be used as the module name.
    pub fn add_from_program(&mut self, program: &Program, source_path: Option<&Path>) {
        let (module_path, decl_span) = if let Some(ref decl) = program.module {
            let path: Vec<String> = decl.path.iter().map(|id| id.name.clone()).collect();
            (path, decl.span.clone())
        } else if let Some(path) = source_path {
            // Use filename as module name
            let name = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("anonymous")
                .to_string();
            (vec![name], crate::ast::Span::default())
        } else {
            return; // No module declaration and no source path
        };

        // Collect node names
        let nodes: Vec<String> = program.nodes.iter().map(|n| n.name.name.clone()).collect();

        // Collect all tags from nodes
        let mut tags = HashSet::new();
        for node in &program.nodes {
            for tag in &node.tags {
                tags.insert(tag.name.clone());
            }
        }

        let entry = ModuleEntry {
            path: module_path.clone(),
            decl_span,
            nodes,
            tags: tags.clone(),
            source_path: source_path.map(|p| p.to_path_buf()),
        };

        let full_path = module_path.join(".");

        // Update inverted tag index
        for tag in &tags {
            self.by_tag
                .entry(tag.clone())
                .or_default()
                .insert(full_path.clone());
        }

        // Insert into tree
        self.tree.insert(&module_path, entry.clone());

        // Insert into flat map
        self.by_path.insert(full_path, entry);
    }

    /// Get a module by its full dotted path
    ///
    /// # Example
    /// ```ignore
    /// let entry = index.get("math.arithmetic");
    /// ```
    pub fn get(&self, path: &str) -> Option<&ModuleEntry> {
        self.by_path.get(path)
    }

    /// Get a module by path components
    pub fn get_by_parts(&self, parts: &[String]) -> Option<&ModuleEntry> {
        self.tree.get(parts)
    }

    /// Find all modules matching a path prefix
    ///
    /// # Example
    /// ```ignore
    /// // Get all modules under "math"
    /// let math_modules = index.find_by_prefix("math");
    /// ```
    pub fn find_by_prefix(&self, prefix: &str) -> Vec<ModuleEntry> {
        let parts: Vec<String> = if prefix.is_empty() {
            Vec::new()
        } else {
            prefix.split('.').map(|s| s.to_string()).collect()
        };
        self.tree.get_by_prefix(&parts)
    }

    /// Find all modules with a specific tag
    ///
    /// # Example
    /// ```ignore
    /// // Find all modules tagged as "pure"
    /// let pure_modules = index.find_by_tag("pure");
    /// ```
    pub fn find_by_tag(&self, tag: &str) -> Vec<&ModuleEntry> {
        if let Some(paths) = self.by_tag.get(tag) {
            paths.iter().filter_map(|p| self.by_path.get(p)).collect()
        } else {
            Vec::new()
        }
    }

    /// Find all modules with any of the specified tags
    pub fn find_by_any_tag(&self, tags: &[&str]) -> Vec<&ModuleEntry> {
        let mut found_paths = HashSet::new();
        for tag in tags {
            if let Some(paths) = self.by_tag.get(*tag) {
                found_paths.extend(paths.iter().cloned());
            }
        }
        found_paths
            .iter()
            .filter_map(|p| self.by_path.get(p))
            .collect()
    }

    /// Find all modules with all of the specified tags
    pub fn find_by_all_tags(&self, tags: &[&str]) -> Vec<&ModuleEntry> {
        if tags.is_empty() {
            return self.all_modules();
        }

        // Start with first tag's modules
        let first_tag = tags[0];
        let initial_paths: HashSet<String> = self
            .by_tag
            .get(first_tag)
            .cloned()
            .unwrap_or_default();

        // Intersect with remaining tags
        let matching_paths = tags[1..].iter().fold(initial_paths, |acc, tag| {
            if let Some(paths) = self.by_tag.get(*tag) {
                acc.intersection(paths).cloned().collect()
            } else {
                HashSet::new()
            }
        });

        matching_paths
            .iter()
            .filter_map(|p| self.by_path.get(p))
            .collect()
    }

    /// Get all indexed modules
    pub fn all_modules(&self) -> Vec<&ModuleEntry> {
        self.by_path.values().collect()
    }

    /// Get all unique tags across all modules
    pub fn all_tags(&self) -> Vec<&str> {
        self.by_tag.keys().map(|s| s.as_str()).collect()
    }

    /// Get count of indexed modules
    pub fn len(&self) -> usize {
        self.by_path.len()
    }

    /// Check if index is empty
    pub fn is_empty(&self) -> bool {
        self.by_path.is_empty()
    }

    /// Get the hierarchical tree structure
    pub fn tree(&self) -> &ModuleTreeNode {
        &self.tree
    }
}

// ========== Module Resolution System ==========

/// A resolved module with its parsed content and dependencies
#[derive(Debug, Clone)]
pub struct ResolvedModule {
    /// The canonical path of this module
    pub path: PathBuf,
    /// The parsed program
    pub program: Program,
    /// Alias for this module (if any)
    pub alias: Option<String>,
}

/// Module resolver for finding and loading BMB modules
pub struct ModuleResolver {
    /// Base directories to search for modules
    search_paths: Vec<PathBuf>,
    /// Cache of loaded modules (path -> program)
    cache: HashMap<PathBuf, Program>,
    /// Currently loading modules (for circular dependency detection)
    loading: HashSet<PathBuf>,
}

impl ModuleResolver {
    /// Create a new module resolver with the given base directory
    pub fn new(base_dir: impl AsRef<Path>) -> Self {
        Self {
            search_paths: vec![base_dir.as_ref().to_path_buf()],
            cache: HashMap::new(),
            loading: HashSet::new(),
        }
    }

    /// Add a search path for modules
    pub fn add_search_path(&mut self, path: impl AsRef<Path>) {
        self.search_paths.push(path.as_ref().to_path_buf());
    }

    /// Resolve all module dependencies for a program
    ///
    /// Returns a map of module names/aliases to their resolved modules
    pub fn resolve_all(&mut self, program: &Program) -> Result<HashMap<String, ResolvedModule>> {
        let mut resolved = HashMap::new();

        for module_use in &program.uses {
            let module = self.resolve_module(module_use)?;
            let name = self.get_module_name(module_use);
            resolved.insert(name, module);
        }

        Ok(resolved)
    }

    /// Resolve a single module import
    pub fn resolve_module(&mut self, module_use: &ModuleUse) -> Result<ResolvedModule> {
        let path = self.find_module_path(&module_use.path)?;

        // Check for circular dependency
        if self.loading.contains(&path) {
            return Err(BmbError::ModuleError {
                message: format!("Circular dependency detected: {}", path.display()),
            });
        }

        // Check cache
        if let Some(program) = self.cache.get(&path) {
            return Ok(ResolvedModule {
                path: path.clone(),
                program: program.clone(),
                alias: module_use.alias.as_ref().map(|id| id.name.clone()),
            });
        }

        // Mark as loading for circular dependency detection
        self.loading.insert(path.clone());

        // Load and parse the module
        let source = std::fs::read_to_string(&path).map_err(|e| BmbError::ModuleError {
            message: format!("Failed to read module {}: {}", path.display(), e),
        })?;

        let program = parser::parse(&source)?;

        // Recursively resolve dependencies
        for sub_use in &program.uses {
            self.resolve_module(sub_use)?;
        }

        // Done loading
        self.loading.remove(&path);

        // Cache the result
        self.cache.insert(path.clone(), program.clone());

        Ok(ResolvedModule {
            path,
            program,
            alias: module_use.alias.as_ref().map(|id| id.name.clone()),
        })
    }

    /// Find the file path for a module
    fn find_module_path(&self, module_path: &ModulePath) -> Result<PathBuf> {
        match module_path {
            ModulePath::FilePath(path_str) => {
                // Direct file path - search relative to search paths
                for base in &self.search_paths {
                    let full_path = base.join(path_str);
                    if full_path.exists() {
                        return Ok(full_path.canonicalize().map_err(|e| BmbError::ModuleError {
                            message: format!("Failed to canonicalize path: {}", e),
                        })?);
                    }
                }
                Err(BmbError::ModuleError {
                    message: format!("Module not found: {}", path_str),
                })
            }
            ModulePath::Name(ident) => {
                // Module name - look for <name>.bmb in search paths
                let filename = format!("{}.bmb", ident.name);
                for base in &self.search_paths {
                    let full_path = base.join(&filename);
                    if full_path.exists() {
                        return Ok(full_path.canonicalize().map_err(|e| BmbError::ModuleError {
                            message: format!("Failed to canonicalize path: {}", e),
                        })?);
                    }
                }
                Err(BmbError::ModuleError {
                    message: format!("Module not found: {}", ident.name),
                })
            }
        }
    }

    /// Get the name to use for a module (alias or derived from path)
    fn get_module_name(&self, module_use: &ModuleUse) -> String {
        if let Some(ref alias) = module_use.alias {
            return alias.name.clone();
        }

        match &module_use.path {
            ModulePath::FilePath(path_str) => {
                // Extract filename without extension
                Path::new(path_str)
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("module")
                    .to_string()
            }
            ModulePath::Name(ident) => ident.name.clone(),
        }
    }
}

/// A merged program with all modules resolved
#[derive(Debug, Clone)]
pub struct MergedProgram {
    /// The main program
    pub main: Program,
    /// Resolved modules by name/alias
    pub modules: HashMap<String, ResolvedModule>,
    /// All nodes from all modules, keyed by qualified name
    pub all_nodes: HashMap<String, Node>,
}

impl MergedProgram {
    /// Create a merged program from a main program and its resolved modules
    pub fn new(main: Program, modules: HashMap<String, ResolvedModule>) -> Self {
        let mut all_nodes = HashMap::new();

        // Add nodes from main program (unqualified)
        for node in &main.nodes {
            all_nodes.insert(node.name.name.clone(), node.clone());
        }

        // Add nodes from imported modules (qualified with module name)
        for (module_name, resolved) in &modules {
            for node in &resolved.program.nodes {
                let qualified_name = format!("{}::{}", module_name, node.name.name);
                all_nodes.insert(qualified_name, node.clone());
            }
        }

        Self {
            main,
            modules,
            all_nodes,
        }
    }

    /// Look up a node by name (qualified or unqualified)
    pub fn get_node(&self, name: &str) -> Option<&Node> {
        self.all_nodes.get(name)
    }

    /// Look up a node by module and function name
    pub fn get_qualified_node(&self, module: &str, name: &str) -> Option<&Node> {
        let qualified = format!("{}::{}", module, name);
        self.all_nodes.get(&qualified)
    }
}

/// Add ModuleError variant to BmbError
/// Note: This needs to be added to lib.rs error enum

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    /// Create a unique temp directory for tests
    fn create_temp_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("bmb_test_{}", name));
        if dir.exists() {
            fs::remove_dir_all(&dir).ok();
        }
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn test_module_resolver_creation() {
        let resolver = ModuleResolver::new(".");
        assert_eq!(resolver.search_paths.len(), 1);
    }

    #[test]
    fn test_module_not_found() {
        let mut resolver = ModuleResolver::new(".");
        let module_use = ModuleUse {
            path: ModulePath::Name(crate::ast::Identifier::new(
                "nonexistent",
                crate::ast::Span::default(),
            )),
            alias: None,
            span: crate::ast::Span::default(),
        };

        let result = resolver.resolve_module(&module_use);
        assert!(result.is_err());
    }

    #[test]
    fn test_resolve_simple_module() {
        let dir = create_temp_dir("resolve_simple");
        let module_path = dir.join("math.bmb");

        // Use "adder" instead of "add" since "add" is a reserved opcode
        let content = "@node adder\n@params a:i32 b:i32\n@returns i32\n  add %r a b\n  ret %r\n";

        fs::write(&module_path, content).unwrap();

        let mut resolver = ModuleResolver::new(&dir);
        let module_use = ModuleUse {
            path: ModulePath::Name(crate::ast::Identifier::new(
                "math",
                crate::ast::Span::default(),
            )),
            alias: None,
            span: crate::ast::Span::default(),
        };

        let result = resolver.resolve_module(&module_use);
        assert!(result.is_ok(), "Module resolution failed: {:?}", result.err());

        let resolved = result.unwrap();
        assert_eq!(resolved.program.nodes.len(), 1);
        assert_eq!(resolved.program.nodes[0].name.name, "adder");

        // Cleanup
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_circular_dependency_detection() {
        let dir = create_temp_dir("circular_dep");

        // Create two modules that depend on each other
        fs::write(
            dir.join("a.bmb"),
            r#"
@use b

@node foo
@params
@returns i32
  ret 1
"#,
        )
        .unwrap();

        fs::write(
            dir.join("b.bmb"),
            r#"
@use a

@node bar
@params
@returns i32
  ret 2
"#,
        )
        .unwrap();

        let mut resolver = ModuleResolver::new(&dir);
        let module_use = ModuleUse {
            path: ModulePath::Name(crate::ast::Identifier::new("a", crate::ast::Span::default())),
            alias: None,
            span: crate::ast::Span::default(),
        };

        let result = resolver.resolve_module(&module_use);
        assert!(result.is_err());
        if let Err(BmbError::ModuleError { message }) = result {
            assert!(message.contains("Circular dependency"));
        } else {
            panic!("Expected ModuleError");
        }

        // Cleanup
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_module_with_alias() {
        let dir = create_temp_dir("module_alias");
        let module_path = dir.join("mathematics.bmb");

        // Use "adder" instead of "add" since "add" is a reserved opcode
        fs::write(
            &module_path,
            r#"@node adder
@params a:i32 b:i32
@returns i32
  add %r a b
  ret %r
"#,
        )
        .unwrap();

        let mut resolver = ModuleResolver::new(&dir);
        let module_use = ModuleUse {
            path: ModulePath::Name(crate::ast::Identifier::new(
                "mathematics",
                crate::ast::Span::default(),
            )),
            alias: Some(crate::ast::Identifier::new("m", crate::ast::Span::default())),
            span: crate::ast::Span::default(),
        };

        let result = resolver.resolve_module(&module_use);
        assert!(result.is_ok(), "Module resolution failed: {:?}", result.err());

        let resolved = result.unwrap();
        assert_eq!(resolved.alias, Some("m".to_string()));

        // Cleanup
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_merged_program() {
        let main = Program {
            module: None,
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: crate::ast::Identifier::new("main", crate::ast::Span::default()),
                tags: vec![],
                params: vec![],
                returns: crate::ast::Type::I32,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: crate::ast::Span::default(),
            }],
        };

        let math_module = ResolvedModule {
            path: PathBuf::from("math.bmb"),
            program: Program {
                module: None,
                imports: vec![],
                uses: vec![],
                structs: vec![],
                enums: vec![],
                nodes: vec![crate::ast::Node {
                    name: crate::ast::Identifier::new("add", crate::ast::Span::default()),
                    tags: vec![],
                    params: vec![],
                    returns: crate::ast::Type::I32,
                    preconditions: vec![],
                    postconditions: vec![],
                    invariants: vec![],
                    variants: vec![],
                    pure: false,
                    requires: vec![],
                    assertions: vec![],
                    tests: vec![],
                    body: vec![],
                    span: crate::ast::Span::default(),
                }],
            },
            alias: None,
        };

        let mut modules = HashMap::new();
        modules.insert("math".to_string(), math_module);

        let merged = MergedProgram::new(main, modules);

        assert!(merged.get_node("main").is_some());
        assert!(merged.get_node("math::add").is_some());
        assert!(merged.get_qualified_node("math", "add").is_some());
    }

    #[test]
    fn test_parse_qualified_call() {
        // Test that qualified function calls parse correctly
        let source = r#"@node caller
@params
@returns i32
  call %r math::adder 1 2
  ret %r
"#;
        let result = crate::parser::parse(source);
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let program = result.unwrap();
        assert_eq!(program.nodes.len(), 1);

        // Check the call statement has a qualified identifier
        let node = &program.nodes[0];
        assert!(!node.body.is_empty());

        if let crate::ast::Instruction::Statement(stmt) = &node.body[0] {
            assert_eq!(stmt.opcode, crate::ast::Opcode::Call);
            // Second operand should be the qualified identifier
            if let crate::ast::Operand::QualifiedIdent { module, name } = &stmt.operands[1] {
                assert_eq!(module.name, "math");
                assert_eq!(name.name, "adder");
            } else {
                panic!("Expected QualifiedIdent, got {:?}", stmt.operands[1]);
            }
        } else {
            panic!("Expected statement, got label");
        }
    }

    #[test]
    fn test_typecheck_qualified_call() {
        // Test that qualified function calls typecheck when module is registered
        use crate::types::typecheck_merged;

        let main = Program {
            module: None,
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: crate::ast::Identifier::new("caller", crate::ast::Span::default()),
                tags: vec![],
                params: vec![],
                returns: crate::ast::Type::I32,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![
                    crate::ast::Instruction::Statement(crate::ast::Statement {
                        opcode: crate::ast::Opcode::Call,
                        operands: vec![
                            crate::ast::Operand::Register(crate::ast::Identifier::new(
                                "r",
                                crate::ast::Span::default(),
                            )),
                            crate::ast::Operand::QualifiedIdent {
                                module: crate::ast::Identifier::new("math", crate::ast::Span::default()),
                                name: crate::ast::Identifier::new("adder", crate::ast::Span::default()),
                            },
                            crate::ast::Operand::IntLiteral(1),
                            crate::ast::Operand::IntLiteral(2),
                        ],
                        span: crate::ast::Span::default(),
                    }),
                    crate::ast::Instruction::Statement(crate::ast::Statement {
                        opcode: crate::ast::Opcode::Ret,
                        operands: vec![crate::ast::Operand::Register(crate::ast::Identifier::new(
                            "r",
                            crate::ast::Span::default(),
                        ))],
                        span: crate::ast::Span::default(),
                    }),
                ],
                span: crate::ast::Span::default(),
            }],
        };

        // Create a module with the adder function
        let math_module = ResolvedModule {
            path: PathBuf::from("math.bmb"),
            program: Program {
                module: None,
                imports: vec![],
                uses: vec![],
                structs: vec![],
                enums: vec![],
                nodes: vec![crate::ast::Node {
                    name: crate::ast::Identifier::new("adder", crate::ast::Span::default()),
                    tags: vec![],
                    params: vec![
                        crate::ast::Parameter {
                            name: crate::ast::Identifier::new("a", crate::ast::Span::default()),
                            ty: crate::ast::Type::I32,
                            span: crate::ast::Span::default(),
                        },
                        crate::ast::Parameter {
                            name: crate::ast::Identifier::new("b", crate::ast::Span::default()),
                            ty: crate::ast::Type::I32,
                            span: crate::ast::Span::default(),
                        },
                    ],
                    returns: crate::ast::Type::I32,
                    preconditions: vec![],
                    postconditions: vec![],
                    invariants: vec![],
                    variants: vec![],
                    pure: false,
                    requires: vec![],
                    assertions: vec![],
                    tests: vec![],
                    body: vec![],
                    span: crate::ast::Span::default(),
                }],
            },
            alias: None,
        };

        let mut modules = HashMap::new();
        modules.insert("math".to_string(), math_module);

        let merged = MergedProgram::new(main, modules);

        // Typecheck should succeed because math::adder is registered
        let result = typecheck_merged(&merged);
        assert!(result.is_ok(), "Typecheck failed: {:?}", result.err());
    }

    // ========== Module Index Tests ==========

    #[test]
    fn test_module_index_creation() {
        let index = ModuleIndex::new();
        assert!(index.is_empty());
        assert_eq!(index.len(), 0);
    }

    #[test]
    fn test_module_index_add_program() {
        let mut index = ModuleIndex::new();

        // Create a program with @module declaration
        let program = Program {
            module: Some(ModuleDecl {
                path: vec![
                    Identifier::new("math", crate::ast::Span::default()),
                    Identifier::new("arithmetic", crate::ast::Span::default()),
                ],
                span: crate::ast::Span::default(),
            }),
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: Identifier::new("sum", crate::ast::Span::default()),
                tags: vec![
                    Identifier::new("pure", crate::ast::Span::default()),
                    Identifier::new("math", crate::ast::Span::default()),
                ],
                params: vec![],
                returns: crate::ast::Type::I32,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: crate::ast::Span::default(),
            }],
        };

        index.add_from_program(&program, Some(Path::new("math.bmb")));

        assert_eq!(index.len(), 1);
        assert!(!index.is_empty());

        // Query by full path
        let entry = index.get("math.arithmetic");
        assert!(entry.is_some());
        let entry = entry.unwrap();
        assert_eq!(entry.path, vec!["math", "arithmetic"]);
        assert_eq!(entry.nodes, vec!["sum"]);
        assert!(entry.tags.contains("pure"));
        assert!(entry.tags.contains("math"));
    }

    #[test]
    fn test_module_index_hierarchical() {
        let mut index = ModuleIndex::new();

        // Add math.arithmetic
        let program1 = Program {
            module: Some(ModuleDecl {
                path: vec![
                    Identifier::new("math", crate::ast::Span::default()),
                    Identifier::new("arithmetic", crate::ast::Span::default()),
                ],
                span: crate::ast::Span::default(),
            }),
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: Identifier::new("sum", crate::ast::Span::default()),
                tags: vec![Identifier::new("pure", crate::ast::Span::default())],
                params: vec![],
                returns: crate::ast::Type::I32,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: crate::ast::Span::default(),
            }],
        };
        index.add_from_program(&program1, None);

        // Add math.geometry
        let program2 = Program {
            module: Some(ModuleDecl {
                path: vec![
                    Identifier::new("math", crate::ast::Span::default()),
                    Identifier::new("geometry", crate::ast::Span::default()),
                ],
                span: crate::ast::Span::default(),
            }),
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: Identifier::new("area", crate::ast::Span::default()),
                tags: vec![Identifier::new("pure", crate::ast::Span::default())],
                params: vec![],
                returns: crate::ast::Type::F64,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: crate::ast::Span::default(),
            }],
        };
        index.add_from_program(&program2, None);

        // Add io.file
        let program3 = Program {
            module: Some(ModuleDecl {
                path: vec![
                    Identifier::new("io", crate::ast::Span::default()),
                    Identifier::new("file", crate::ast::Span::default()),
                ],
                span: crate::ast::Span::default(),
            }),
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: Identifier::new("read", crate::ast::Span::default()),
                tags: vec![Identifier::new("io", crate::ast::Span::default())],
                params: vec![],
                returns: crate::ast::Type::I32,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: crate::ast::Span::default(),
            }],
        };
        index.add_from_program(&program3, None);

        assert_eq!(index.len(), 3);

        // Find all modules under "math"
        let math_modules = index.find_by_prefix("math");
        assert_eq!(math_modules.len(), 2);

        // Find all modules (empty prefix)
        let all_modules = index.find_by_prefix("");
        assert_eq!(all_modules.len(), 3);
    }

    #[test]
    fn test_module_index_tag_query() {
        let mut index = ModuleIndex::new();

        // Add module with "pure" tag
        let program1 = Program {
            module: Some(ModuleDecl {
                path: vec![Identifier::new("math", crate::ast::Span::default())],
                span: crate::ast::Span::default(),
            }),
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: Identifier::new("sum", crate::ast::Span::default()),
                tags: vec![
                    Identifier::new("pure", crate::ast::Span::default()),
                    Identifier::new("safe", crate::ast::Span::default()),
                ],
                params: vec![],
                returns: crate::ast::Type::I32,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: crate::ast::Span::default(),
            }],
        };
        index.add_from_program(&program1, None);

        // Add module with "io" tag
        let program2 = Program {
            module: Some(ModuleDecl {
                path: vec![Identifier::new("io", crate::ast::Span::default())],
                span: crate::ast::Span::default(),
            }),
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: Identifier::new("read", crate::ast::Span::default()),
                tags: vec![
                    Identifier::new("io", crate::ast::Span::default()),
                    Identifier::new("safe", crate::ast::Span::default()),
                ],
                params: vec![],
                returns: crate::ast::Type::I32,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: crate::ast::Span::default(),
            }],
        };
        index.add_from_program(&program2, None);

        // Find by single tag
        let pure_modules = index.find_by_tag("pure");
        assert_eq!(pure_modules.len(), 1);
        assert_eq!(pure_modules[0].full_path(), "math");

        let safe_modules = index.find_by_tag("safe");
        assert_eq!(safe_modules.len(), 2);

        // Find by any tag
        let any_modules = index.find_by_any_tag(&["pure", "io"]);
        assert_eq!(any_modules.len(), 2);

        // Find by all tags
        let both_modules = index.find_by_all_tags(&["pure", "safe"]);
        assert_eq!(both_modules.len(), 1);
        assert_eq!(both_modules[0].full_path(), "math");

        // All tags list
        let all_tags = index.all_tags();
        assert!(all_tags.contains(&"pure"));
        assert!(all_tags.contains(&"safe"));
        assert!(all_tags.contains(&"io"));
    }

    #[test]
    fn test_module_index_fallback_to_filename() {
        let mut index = ModuleIndex::new();

        // Program without @module declaration
        let program = Program {
            module: None,
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: Identifier::new("helper", crate::ast::Span::default()),
                tags: vec![],
                params: vec![],
                returns: crate::ast::Type::I32,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: crate::ast::Span::default(),
            }],
        };

        // Should use filename as module name
        index.add_from_program(&program, Some(Path::new("/path/to/utils.bmb")));

        let entry = index.get("utils");
        assert!(entry.is_some());
        assert_eq!(entry.unwrap().nodes, vec!["helper"]);
    }
}
