//! BMB Language Server
//!
//! A Language Server Protocol implementation for BMB.
//!
//! "Omission is guessing, and guessing is error."
//! - The LSP helps developers catch errors early.

use dashmap::DashMap;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use bmb::ast::Program;
use bmb::lint::{lint, Severity};
use bmb::parser;

/// Document state stored per file
struct Document {
    content: String,
    ast: Option<Program>,
    #[allow(dead_code)]
    version: i32,
}

/// BMB Language Server backend
struct BmbLanguageServer {
    client: Client,
    documents: DashMap<Url, Document>,
}

impl BmbLanguageServer {
    fn new(client: Client) -> Self {
        Self {
            client,
            documents: DashMap::new(),
        }
    }

    /// Parse a document and publish diagnostics
    async fn analyze_document(&self, uri: Url, text: String, version: i32) {
        let mut diagnostics = Vec::new();

        // Try to parse the document
        match parser::parse(&text) {
            Ok(ast) => {
                // Successful parse - run linter
                let warnings = lint(&ast);
                for warning in warnings {
                    let range = if let Some(line) = warning.line {
                        Range {
                            start: Position {
                                line: (line.saturating_sub(1)) as u32,
                                character: 0,
                            },
                            end: Position {
                                line: (line.saturating_sub(1)) as u32,
                                character: 100,
                            },
                        }
                    } else {
                        Range::default()
                    };

                    let severity = match warning.severity {
                        Severity::Warning => DiagnosticSeverity::WARNING,
                        Severity::Style => DiagnosticSeverity::HINT,
                        Severity::Info => DiagnosticSeverity::INFORMATION,
                    };

                    let mut diagnostic = Diagnostic {
                        range,
                        severity: Some(severity),
                        code: Some(NumberOrString::String(warning.code.to_string())),
                        source: Some("bmb-lint".to_string()),
                        message: warning.message.clone(),
                        ..Default::default()
                    };

                    if let Some(suggestion) = &warning.suggestion {
                        diagnostic.related_information = Some(vec![DiagnosticRelatedInformation {
                            location: Location {
                                uri: uri.clone(),
                                range,
                            },
                            message: format!("help: {}", suggestion),
                        }]);
                    }

                    diagnostics.push(diagnostic);
                }

                // Store the parsed AST
                self.documents.insert(
                    uri.clone(),
                    Document {
                        content: text,
                        ast: Some(ast),
                        version,
                    },
                );
            }
            Err(e) => {
                // Parse error - create diagnostic
                let (line, column, message) = match &e {
                    bmb::BmbError::ParseError {
                        line,
                        column,
                        message,
                    } => (*line, *column, message.clone()),
                    _ => (1, 1, e.to_string()),
                };

                diagnostics.push(Diagnostic {
                    range: Range {
                        start: Position {
                            line: (line.saturating_sub(1)) as u32,
                            character: (column.saturating_sub(1)) as u32,
                        },
                        end: Position {
                            line: (line.saturating_sub(1)) as u32,
                            character: (column + 20) as u32,
                        },
                    },
                    severity: Some(DiagnosticSeverity::ERROR),
                    source: Some("bmb".to_string()),
                    message,
                    ..Default::default()
                });

                // Store without AST
                self.documents.insert(
                    uri.clone(),
                    Document {
                        content: text,
                        ast: None,
                        version,
                    },
                );
            }
        }

        // Publish diagnostics
        self.client
            .publish_diagnostics(uri, diagnostics, Some(version))
            .await;
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for BmbLanguageServer {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec!["@".to_string(), "%".to_string(), "_".to_string()]),
                    ..Default::default()
                }),
                definition_provider: Some(OneOf::Left(true)),
                document_formatting_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "bmb-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "BMB Language Server initialized!")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;

        self.analyze_document(uri, text, version).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;

        // We use full sync, so there should be exactly one change with the full text
        if let Some(change) = params.content_changes.into_iter().last() {
            self.analyze_document(uri, change.text, version).await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.documents.remove(&params.text_document.uri);
        // Clear diagnostics
        self.client
            .publish_diagnostics(params.text_document.uri, vec![], None)
            .await;
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        if let Some(doc) = self.documents.get(uri) {
            // Get the word at the cursor position
            let lines: Vec<&str> = doc.content.lines().collect();
            if let Some(line) = lines.get(position.line as usize) {
                let col = position.character as usize;
                let word = get_word_at_position(line, col);

                // Provide hover info for keywords and opcodes
                let info = match word.as_str() {
                    "@node" => Some("Defines a function node"),
                    "@params" => Some("Function parameters declaration"),
                    "@returns" => Some("Function return type"),
                    "@pre" => Some("Precondition (must be true when function is called)"),
                    "@post" => Some("Postcondition (must be true when function returns)"),
                    "@invariant" => Some("Loop invariant (must be true at every iteration)"),
                    "@struct" => Some("Structure type definition"),
                    "@enum" => Some("Enumeration type definition"),
                    "@import" => Some("External function import"),
                    "add" => Some("Addition: add %dest a b → dest = a + b"),
                    "sub" => Some("Subtraction: sub %dest a b → dest = a - b"),
                    "mul" => Some("Multiplication: mul %dest a b → dest = a * b"),
                    "div" => Some("Division: div %dest a b → dest = a / b"),
                    "mod" => Some("Modulo: mod %dest a b → dest = a % b"),
                    "eq" => Some("Equality: eq %dest a b → dest = (a == b)"),
                    "ne" => Some("Not equal: ne %dest a b → dest = (a != b)"),
                    "lt" => Some("Less than: lt %dest a b → dest = (a < b)"),
                    "le" => Some("Less or equal: le %dest a b → dest = (a <= b)"),
                    "gt" => Some("Greater than: gt %dest a b → dest = (a > b)"),
                    "ge" => Some("Greater or equal: ge %dest a b → dest = (a >= b)"),
                    "mov" => Some("Move: mov %dest value → dest = value"),
                    "ret" => Some("Return: ret %value → returns value from function"),
                    "jmp" => Some("Jump: jmp _label → unconditional jump to label"),
                    "jif" => Some("Jump if: jif %cond _label → jump if condition is true"),
                    "call" => Some("Call: call %dest func args... → call function"),
                    "xcall" => Some("External call: xcall func args... → call imported function"),
                    "load" => Some("Load: load %dest src → load value from memory"),
                    "store" => Some("Store: store dest %src → store value to memory"),
                    "print" => Some("Print: print %value → print value to output"),
                    "i32" => Some("32-bit signed integer type"),
                    "i64" => Some("64-bit signed integer type"),
                    "f32" => Some("32-bit floating point type"),
                    "f64" => Some("64-bit floating point type"),
                    "bool" => Some("Boolean type (true/false)"),
                    "void" => Some("Void type (no return value)"),
                    "old" => Some("old(expr) - reference to pre-state value in postconditions"),
                    _ => None,
                };

                if let Some(description) = info {
                    return Ok(Some(Hover {
                        contents: HoverContents::Markup(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: format!("**{}**\n\n{}", word, description),
                        }),
                        range: None,
                    }));
                }
            }
        }

        Ok(None)
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        let mut items = Vec::new();

        if let Some(doc) = self.documents.get(uri) {
            let lines: Vec<&str> = doc.content.lines().collect();
            if let Some(line) = lines.get(position.line as usize) {
                let prefix = &line[..position.character as usize];

                // Complete directives
                if prefix.ends_with('@') || prefix.trim().is_empty() {
                    items.extend(vec![
                        CompletionItem {
                            label: "@node".to_string(),
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("Define a function".to_string()),
                            insert_text: Some("node ${1:name}\n@params ${2}\n@returns ${3:i32}\n\n  $0".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "@params".to_string(),
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("Parameter declaration".to_string()),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "@returns".to_string(),
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("Return type declaration".to_string()),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "@pre".to_string(),
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("Precondition".to_string()),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "@post".to_string(),
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("Postcondition".to_string()),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "@invariant".to_string(),
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("Loop invariant".to_string()),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "@struct".to_string(),
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("Structure definition".to_string()),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "@enum".to_string(),
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("Enumeration definition".to_string()),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "@import".to_string(),
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("External function import".to_string()),
                            ..Default::default()
                        },
                    ]);
                }

                // Complete opcodes (after leading whitespace)
                if prefix.trim().is_empty() && prefix.starts_with(' ') {
                    items.extend(vec![
                        CompletionItem {
                            label: "add".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Addition".to_string()),
                            insert_text: Some("add %${1:dest} ${2:a} ${3:b}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "sub".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Subtraction".to_string()),
                            insert_text: Some("sub %${1:dest} ${2:a} ${3:b}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "mul".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Multiplication".to_string()),
                            insert_text: Some("mul %${1:dest} ${2:a} ${3:b}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "div".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Division".to_string()),
                            insert_text: Some("div %${1:dest} ${2:a} ${3:b}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "mod".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Modulo".to_string()),
                            insert_text: Some("mod %${1:dest} ${2:a} ${3:b}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "mov".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Move value".to_string()),
                            insert_text: Some("mov %${1:dest} ${2:value}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "ret".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Return".to_string()),
                            insert_text: Some("ret %${1:value}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "jmp".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Jump".to_string()),
                            insert_text: Some("jmp _${1:label}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "jif".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Jump if true".to_string()),
                            insert_text: Some("jif %${1:cond} _${2:label}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "call".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Call function".to_string()),
                            insert_text: Some("call %${1:result} ${2:func} ${3:args}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "eq".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Equality comparison".to_string()),
                            insert_text: Some("eq %${1:dest} ${2:a} ${3:b}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "lt".to_string(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("Less than comparison".to_string()),
                            insert_text: Some("lt %${1:dest} ${2:a} ${3:b}".to_string()),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        },
                    ]);
                }

                // Complete types after :
                if prefix.ends_with(':') {
                    items.extend(vec![
                        CompletionItem {
                            label: "i32".to_string(),
                            kind: Some(CompletionItemKind::TYPE_PARAMETER),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "i64".to_string(),
                            kind: Some(CompletionItemKind::TYPE_PARAMETER),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "f32".to_string(),
                            kind: Some(CompletionItemKind::TYPE_PARAMETER),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "f64".to_string(),
                            kind: Some(CompletionItemKind::TYPE_PARAMETER),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "bool".to_string(),
                            kind: Some(CompletionItemKind::TYPE_PARAMETER),
                            ..Default::default()
                        },
                        CompletionItem {
                            label: "void".to_string(),
                            kind: Some(CompletionItemKind::TYPE_PARAMETER),
                            ..Default::default()
                        },
                    ]);
                }
            }
        }

        if items.is_empty() {
            Ok(None)
        } else {
            Ok(Some(CompletionResponse::Array(items)))
        }
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let uri = &params.text_document.uri;

        if let Some(doc) = self.documents.get(uri) {
            if let Some(ref ast) = doc.ast {
                let formatted = bmb::fmt::format_program(ast);
                let line_count = doc.content.lines().count();

                // Replace entire document
                return Ok(Some(vec![TextEdit {
                    range: Range {
                        start: Position { line: 0, character: 0 },
                        end: Position {
                            line: line_count as u32,
                            character: 0,
                        },
                    },
                    new_text: formatted,
                }]));
            }
        }

        Ok(None)
    }
}

/// Get the word at the given position in a line
fn get_word_at_position(line: &str, col: usize) -> String {
    let chars: Vec<char> = line.chars().collect();
    let col = col.min(chars.len());

    // Find word start
    let mut start = col;
    while start > 0 && (chars[start - 1].is_alphanumeric() || chars[start - 1] == '_' || chars[start - 1] == '@') {
        start -= 1;
    }

    // Find word end
    let mut end = col;
    while end < chars.len() && (chars[end].is_alphanumeric() || chars[end] == '_') {
        end += 1;
    }

    chars[start..end].iter().collect()
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(BmbLanguageServer::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}
