use std::borrow::Borrow;
use std::path::Path;
use std::rc::Rc;

use lsp_types::{
    request::Completion, request::GotoDefinition, request::Initialize,
    request::SemanticTokensFullRequest, DidChangeTextDocumentParams, DidChangeWatchedFilesParams,
    DidOpenTextDocumentParams, GotoDefinitionParams, GotoDefinitionResponse, Location, Position,
    Range, Url,
};

use lsp_server::{ErrorCode, Message, RequestId, Response};

use crate::compiler::lsp::completion::LSPCompletionRequestHandler;
use crate::compiler::lsp::patch::{
    compute_comment_lines, split_text, LSPServiceProviderApplyDocumentPatch,
};
use crate::compiler::lsp::semtok::LSPSemtokRequestHandler;
use crate::compiler::lsp::types::{cast, ConfigJson, DocData, InitState, LSPServiceProvider};
use crate::compiler::sexp::decode_string;
use crate::compiler::srcloc::Srcloc;

pub trait LSPServiceMessageHandler {
    fn handle_message(&mut self, msg: &Message) -> Result<Vec<Message>, String>;
    fn handle_message_from_string(&mut self, msg: String) -> Result<Vec<Message>, String>;
}

fn is_real_include(l: &Srcloc) -> bool {
    let borrowed_file: &String = l.file.borrow();
    !borrowed_file.starts_with('*')
}

impl LSPServiceProvider {
    fn goto_definition(
        &mut self,
        id: RequestId,
        params: &GotoDefinitionParams,
    ) -> Result<Vec<Message>, String> {
        let mut res = Vec::new();
        let mut goto_response = None;
        let docname = params
            .text_document_position_params
            .text_document
            .uri
            .to_string();
        let docpos = params.text_document_position_params.position;
        let wantloc = Srcloc::new(
            Rc::new(docname.clone()),
            (docpos.line + 1) as usize,
            (docpos.character + 1) as usize,
        );
        if let Some(defs) = self.goto_defs.get(&docname) {
            for kv in defs.iter() {
                if is_real_include(kv.1) && kv.0.loc.overlap(&wantloc) {
                    let filename: &String = kv.1.file.borrow();
                    goto_response = Some(Location {
                        uri: Url::parse(filename).unwrap(),
                        range: Range {
                            start: Position {
                                line: (kv.1.line - 1) as u32,
                                character: (kv.1.col - 1) as u32,
                            },
                            end: Position {
                                line: (kv.1.line - 1) as u32,
                                character: (kv.1.col + kv.1.len() - 1) as u32,
                            },
                        },
                    });
                    break;
                }
            }
        }
        let result = goto_response.map(GotoDefinitionResponse::Scalar);
        let result = serde_json::to_value(&result).unwrap();
        let resp = Response {
            id,
            result: Some(result),
            error: None,
        };
        res.push(Message::Response(resp));

        Ok(res)
    }

    fn reconfigure(&mut self) -> Option<ConfigJson> {
        self.get_config_path()
            .and_then(|config_path| self.fs.read(&config_path).ok())
            .and_then(|config_data| serde_json::from_str(&decode_string(&config_data)).ok())
            .map(|config: ConfigJson| {
                let mut result = config.clone();
                result.include_paths.clear();

                for p in config.include_paths.iter() {
                    if p.starts_with('.') {
                        if let Some(path_str) = self.get_relative_path(p) {
                            result.include_paths.push(path_str.to_owned());
                        }
                    } else if let Some(ps) = Path::new(p).to_str() {
                        result.include_paths.push(ps.to_owned());
                    }
                }

                result
            })
    }
}

impl LSPServiceMessageHandler for LSPServiceProvider {
    fn handle_message(&mut self, msg: &Message) -> Result<Vec<Message>, String> {
        // Handle initialization.
        if self.init.is_none() {
            if let Message::Request(req) = msg {
                if req.method == "initialize" {
                    if let Ok((_, params)) = cast::<Initialize>(req.clone()) {
                        self.init = Some(InitState::Initialized(Rc::new(params)));
                        // Try to read the config data
                        if let Some(config) = self.reconfigure() {
                            // We have a config file and can read the filesystem.
                            self.config = config;
                        }

                        let server_capabilities = LSPServiceProvider::get_capabilities();

                        let initialize_data = serde_json::json!({
                            "capabilities": server_capabilities,
                            "serverInfo": {
                                "name": "chialisp-lsp",
                                "version": "0.1"
                            }
                        });

                        let resp = Response::new_ok(req.id.clone(), initialize_data);

                        return Ok(vec![Message::Response(resp)]);
                    }
                } else {
                    let resp = Response::new_err(
                        req.id.clone(),
                        ErrorCode::ServerNotInitialized as i32,
                        format!("expected initialize request, got {:?}", req),
                    );
                    return Ok(vec![Message::Response(resp)]);
                }
            }
        }

        match msg {
            Message::Request(req) => {
                if let Ok((id, params)) = cast::<SemanticTokensFullRequest>(req.clone()) {
                    return self.handle_semantic_tokens(id, &params);
                } else if let Ok((id, params)) = cast::<GotoDefinition>(req.clone()) {
                    return self.goto_definition(id, &params);
                } else if let Ok((id, params)) = cast::<Completion>(req.clone()) {
                    return self.handle_completion_request(id, &params);
                } else {
                    eprintln!("unknown request {:?}", req);
                };
                // ...
            }
            Message::Response(resp) => {
                eprintln!("got response: {:?}", resp);
            }
            Message::Notification(not) => {
                eprintln!("got notification: {:?}", not);
                if not.method == "textDocument/didOpen" {
                    let stringified_params = serde_json::to_string(&not.params).unwrap();
                    if let Ok(params) =
                        serde_json::from_str::<DidOpenTextDocumentParams>(&stringified_params)
                    {
                        let doc_data = split_text(&params.text_document.text);
                        let comments = compute_comment_lines(&doc_data);
                        self.save_doc(
                            params.text_document.uri.to_string(),
                            DocData {
                                text: doc_data,
                                version: params.text_document.version,
                                comments,
                            },
                        );
                    } else {
                        eprintln!("cast failed in didOpen");
                    }
                } else if not.method == "workspace/didChangeWatchedFiles" {
                    let stringified_params = serde_json::to_string(&not.params).unwrap();
                    if let Ok(params) =
                        serde_json::from_str::<DidChangeWatchedFilesParams>(&stringified_params)
                    {
                        for change in params.changes.iter() {
                            let doc_id = change.uri.to_string();

                            if doc_id.ends_with("chialisp.json") {
                                if let Some(config) = self.reconfigure() {
                                    // We have a config file and can read the filesystem.
                                    eprintln!("reconfigured");
                                    self.config = config;
                                    self.parsed_documents.clear();
                                    self.goto_defs.clear();
                                }
                            }
                        }
                    }
                } else if not.method == "textDocument/didChange" {
                    let stringified_params = serde_json::to_string(&not.params).unwrap();
                    if let Ok(params) =
                        serde_json::from_str::<DidChangeTextDocumentParams>(&stringified_params)
                    {
                        let doc_id = params.text_document.uri.to_string();

                        if doc_id.ends_with("chialisp.json") {
                            if let Some(config) = self.reconfigure() {
                                // We have a config file and can read the filesystem.
                                eprintln!("reconfigured");
                                self.config = config;
                            }
                        }

                        self.apply_document_patch(
                            &doc_id,
                            params.text_document.version,
                            &params.content_changes,
                        );
                    } else {
                        eprintln!("case failed in didChange");
                    }
                } else {
                    eprintln!("not sure what we got: {:?}", not);
                }
            }
        }

        Ok(vec![])
    }

    fn handle_message_from_string(&mut self, msg: String) -> Result<Vec<Message>, String> {
        if let Ok(input_msg) = serde_json::from_str::<Message>(&msg) {
            self.handle_message(&input_msg)
        } else {
            Err("Could not decode as json message".to_string())
        }
    }
}
