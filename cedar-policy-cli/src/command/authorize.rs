/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use std::{fs, path::Path, time::Instant};

use cedar_policy::{Authorizer, Decision, Entities, PolicySet, Response};
use clap::Args;
use miette::Report;

use crate::{load_entities, CedarExitCode, OptionalSchemaArgs, PoliciesArgs, RequestArgs};
use crate::utils::poltree_cache_path;

#[derive(Args, Debug)]
pub struct AuthorizeArgs {
    /// Request args (incorporated by reference)
    #[command(flatten)]
    pub request: RequestArgs,
    /// Policies args (incorporated by reference)
    #[command(flatten)]
    pub policies: PoliciesArgs,
    /// Schema args (incorporated by reference)
    ///
    /// Used to populate the store with action entities and for schema-based
    /// parsing of entity hierarchy, if present
    #[command(flatten)]
    pub schema: OptionalSchemaArgs,
    /// File containing JSON representation of the Cedar entity hierarchy
    #[arg(long = "entities", value_name = "FILE")]
    pub entities_file: String,
    /// More verbose output. (For instance, indicate which policies applied to the request, if any.)
    #[arg(short, long)]
    pub verbose: bool,
    /// Time authorization and report timing information
    #[arg(short, long)]
    pub timing: bool,
    /// Use the PolTree-based authorizer path
    #[arg(long = "poltree")]
    pub use_poltree: bool,
}

pub fn authorize(args: &AuthorizeArgs) -> CedarExitCode {
    println!();
    let ans = execute_request(
        &args.request,
        &args.policies,
        &args.entities_file,
        &args.schema,
        args.timing,
        args.use_poltree,
    );
    match ans {
        Ok(ans) => {
            let status = match ans.decision() {
                Decision::Allow => {
                    println!("ALLOW");
                    CedarExitCode::Success
                }
                Decision::Deny => {
                    println!("DENY");
                    CedarExitCode::AuthorizeDeny
                }
            };
            if ans.diagnostics().errors().peekable().peek().is_some() {
                println!();
                for err in ans.diagnostics().errors() {
                    println!("{err}");
                }
            }
            if args.verbose {
                println!();
                if ans.diagnostics().reason().peekable().peek().is_none() {
                    println!("note: no policies applied to this request");
                } else {
                    println!("note: this decision was due to the following policies:");
                    for reason in ans.diagnostics().reason() {
                        println!("  {reason}");
                    }
                    println!();
                }
            }
            status
        }
        Err(errs) => {
            for err in errs {
                println!("{err:?}");
            }
            CedarExitCode::Failure
        }
    }
}

/// This uses the Cedar API to call the authorization engine.
fn execute_request(
    request: &RequestArgs,
    policies_args: &PoliciesArgs,
    entities_filename: impl AsRef<Path>,
    schema: &OptionalSchemaArgs,
    compute_duration: bool,
    use_poltree: bool,
) -> Result<Response, Vec<Report>> {
    let mut errs = vec![];
    let schema_file_for_cache = schema.schema_file.clone();
    let policy_set = match policies_args.get_policy_set() {
        Ok(pset) => pset,
        Err(e) => {
            errs.push(e);
            PolicySet::new()
        }
    };
    let schema = match schema.get_schema() {
        Ok(opt) => opt,
        Err(e) => {
            errs.push(e);
            None
        }
    };
    let entities = match load_entities(entities_filename.as_ref(), schema.as_ref()) {
        Ok(entities) => entities,
        Err(e) => {
            errs.push(e);
            Entities::empty()
        }
    };
    match request.get_request(schema.as_ref()) {
        Ok(request) if errs.is_empty() => {
            let authorizer = Authorizer::new();
            let ans = if use_poltree {
                let tree_build_start = Instant::now();
                let cache_path = match poltree_cache_path(
                    policies_args,
                    entities_filename.as_ref(),
                    schema_file_for_cache.as_deref(),
                ) {
                    Ok(path) => path,
                    Err(_) => None,
                };
                let mut cache_hit = false;
                let mut cache_read_dur: Option<std::time::Duration> = None;
                let mut cache_deser_dur: Option<std::time::Duration> = None;

                let tree_authorizer = if let Some(cache_path) = cache_path.as_ref() {
                    if cache_path.exists() {
                        // Measure read and deserialize separately so we can see where time goes
                        let read_start = Instant::now();
                        match fs::read(cache_path) {
                            Ok(bytes) => {
                                let read_dur = read_start.elapsed();
                                let deser_start = Instant::now();
                                match authorizer.prepare_from_serialized(&policy_set, &entities, &bytes) {
                                    Ok(tree) => {
                                        let deser_dur = deser_start.elapsed();
                                        cache_hit = true;
                                        cache_read_dur = Some(read_dur);
                                        cache_deser_dur = Some(deser_dur);
                                        if compute_duration {
                                            println!(
                                                "Cache read (micro seconds) : {}",
                                                read_dur.as_micros()
                                            );
                                            println!(
                                                "Cache deserialize (micro seconds) : {}",
                                                deser_dur.as_micros()
                                            );
                                        }
                                        tree
                                    }
                                    Err(_) => {
                                        let tree = authorizer.prepare(&policy_set, &entities);
                                        if let Ok(bytes) = tree.serialize_poltree() {
                                            let _ = fs::write(cache_path, bytes);
                                        }
                                        tree
                                    }
                                }
                            }
                            Err(_) => {
                                let tree = authorizer.prepare(&policy_set, &entities);
                                if let Ok(bytes) = tree.serialize_poltree() {
                                    let _ = fs::write(cache_path, bytes);
                                }
                                tree
                            }
                        }
                    } else {
                        let tree = authorizer.prepare(&policy_set, &entities);
                        if let Ok(bytes) = tree.serialize_poltree() {
                            let _ = fs::write(cache_path, bytes);
                        }
                        tree
                    }
                } else {
                    authorizer.prepare(&policy_set, &entities)
                };

                let tree_build_dur = if cache_hit {
                    // Sum read + deserialize durations when cache was used (fallback to total elapsed)
                    match (cache_read_dur, cache_deser_dur) {
                        (Some(r), Some(d)) => r + d,
                        _ => tree_build_start.elapsed(),
                    }
                } else {
                    tree_build_start.elapsed()
                };

                let tree_eval_start = Instant::now();
                let response = tree_authorizer.is_authorized(&request);
                let tree_eval_dur = tree_eval_start.elapsed();
                if compute_duration {
                    println!("Tree Cache Hit               : {cache_hit}");
                    if cache_hit {
                        println!(
                            "Tree Load Time (micro seconds) : {}",
                            tree_build_dur.as_micros()
                        );
                    } else {
                        println!(
                            "Tree Build Time (micro seconds) : {}",
                            tree_build_dur.as_micros()
                        );
                    }
                    println!(
                        "Tree Evaluation Time (micro seconds) : {}",
                        tree_eval_dur.as_micros()
                    );
                }
                response
            } else {
                let auth_start = Instant::now();
                let response = authorizer.is_authorized(&request, &policy_set, &entities);
                let auth_dur = auth_start.elapsed();
                if compute_duration {
                    println!(
                        "Authorization Time (micro seconds) : {}",
                        auth_dur.as_micros()
                    );
                }
                response
            };
            Ok(ans)
        }
        Ok(_) => Err(errs),
        Err(e) => {
            errs.push(e.wrap_err("failed to parse request"));
            Err(errs)
        }
    }
}
