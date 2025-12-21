//! Module system for BMB
//!
//! Handles module resolution, loading, and dependency management.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::ast::{ModulePath, ModuleUse, Node, Program};
use crate::{parser, BmbError, Result};

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
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: crate::ast::Identifier::new("main", crate::ast::Span::default()),
                params: vec![],
                returns: crate::ast::Type::I32,
                precondition: None,
                postcondition: None,
                invariants: vec![],
                body: vec![],
                span: crate::ast::Span::default(),
            }],
        };

        let math_module = ResolvedModule {
            path: PathBuf::from("math.bmb"),
            program: Program {
                imports: vec![],
                uses: vec![],
                structs: vec![],
                enums: vec![],
                nodes: vec![crate::ast::Node {
                    name: crate::ast::Identifier::new("add", crate::ast::Span::default()),
                    params: vec![],
                    returns: crate::ast::Type::I32,
                    precondition: None,
                    postcondition: None,
                    invariants: vec![],
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
            imports: vec![],
            uses: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![crate::ast::Node {
                name: crate::ast::Identifier::new("caller", crate::ast::Span::default()),
                params: vec![],
                returns: crate::ast::Type::I32,
                precondition: None,
                postcondition: None,
                invariants: vec![],
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
                imports: vec![],
                uses: vec![],
                structs: vec![],
                enums: vec![],
                nodes: vec![crate::ast::Node {
                    name: crate::ast::Identifier::new("adder", crate::ast::Span::default()),
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
                    precondition: None,
                    postcondition: None,
                    invariants: vec![],
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
}
