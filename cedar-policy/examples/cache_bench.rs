use cedar_policy::{
    Authorizer, CachedAuthorizer, Context, Decision, Entities, EntityUid, PolicySet, Request,
};
use serde::Deserialize;
use std::env;
use std::fs;
use std::path::Path;
use std::str::FromStr;
use std::time::Instant;

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonRequest {
    principal: serde_json::Value,
    action: serde_json::Value,
    resource: serde_json::Value,
    context: serde_json::Value,
}

fn parse_entity_uid(value: serde_json::Value, label: &str) -> EntityUid {
    EntityUid::from_json(value).unwrap_or_else(|e| panic!("failed to parse {label}: {e}"))
}

fn load_policy_set(path: &Path) -> PolicySet {
    let src = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read policy file {}: {e}", path.display()));
    PolicySet::from_str(&src).unwrap_or_else(|e| panic!("failed to parse policies: {e}"))
}

fn load_entities(path: &Path) -> Entities {
    let src = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read entities file {}: {e}", path.display()));
    Entities::from_json_str(&src, None).unwrap_or_else(|e| panic!("failed to parse entities: {e}"))
}

fn load_requests(path: &Path) -> Vec<Request> {
    let src = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read requests file {}: {e}", path.display()));
    let json_requests: Vec<JsonRequest> = serde_json::from_str(&src)
        .unwrap_or_else(|e| panic!("failed to parse requests json: {e}"));
    json_requests
        .into_iter()
        .enumerate()
        .map(|(idx, req)| {
            let principal = parse_entity_uid(req.principal, "principal");
            let action = parse_entity_uid(req.action, "action");
            let resource = parse_entity_uid(req.resource, "resource");
            let context = Context::from_json_value(req.context, None)
                .unwrap_or_else(|e| panic!("failed to parse context for request {idx}: {e}"));
            Request::new(principal, action, resource, context, None)
                .unwrap_or_else(|e| panic!("failed to build request {idx}: {e}"))
        })
        .collect()
}

fn bench_normal(
    authorizer: &Authorizer,
    policies: &PolicySet,
    entities: &Entities,
    requests: &[Request],
) -> (std::time::Duration, u64) {
    let mut allow_count = 0u64;
    let start = Instant::now();
    for request in requests {
        let response = authorizer.is_authorized(request, policies, entities);
        if response.decision() == Decision::Allow {
            allow_count += 1;
        }
        std::hint::black_box(response);
    }
    (start.elapsed(), allow_count)
}

fn bench_cached(
    authorizer: &CachedAuthorizer,
    requests: &[Request],
) -> (std::time::Duration, u64) {
    let mut allow_count = 0u64;
    let start = Instant::now();
    for request in requests {
        let response = authorizer.is_authorized(request);
        if response.decision() == Decision::Allow {
            allow_count += 1;
        }
        std::hint::black_box(response);
    }
    (start.elapsed(), allow_count)
}

fn micros_per_request(duration: std::time::Duration, requests: usize) -> f64 {
    if requests == 0 {
        return 0.0;
    }
    duration.as_secs_f64() * 1_000_000.0 / requests as f64
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 4 {
        eprintln!(
            "Usage: {} <policy.cedar> <entities.json> <requests.json>",
            args[0]
        );
        eprintln!("Requests JSON format: an array of objects with principal/action/resource/context.");
                eprintln!(
                        "Example:\n[\n  {{\n    \"principal\": {{ \"type\": \"User\", \"id\": \"alice\" }},\n    \"action\": {{ \"type\": \"Action\", \"id\": \"view\" }},\n    \"resource\": {{ \"type\": \"Photo\", \"id\": \"eng-public-us-alpha-1\" }},\n    \"context\": {{}}\n  }}\n]\n"
                );
        std::process::exit(2);
    }

    let policy_path = Path::new(&args[1]);
    let entities_path = Path::new(&args[2]);
    let requests_path = Path::new(&args[3]);
    let policies = load_policy_set(policy_path);
    let entities = load_entities(entities_path);
    let requests = load_requests(requests_path);
    if requests.is_empty() {
        panic!("no requests provided");
    }

    let normal_authorizer = Authorizer::new();
    let cached_authorizer = CachedAuthorizer::new_with_cache_files(
        policies.clone(),
        entities.clone(),
        policy_path,
        entities_path,
        None::<&Path>,
        None::<&Path>,
    )
    .unwrap_or_else(|e| panic!("failed to initialize cached authorizer: {e}"));

    let (normal_dur, normal_allow) =
        bench_normal(&normal_authorizer, &policies, &entities, &requests);
    let (cached_dur, cached_allow) =
        bench_cached(&cached_authorizer, &requests);

    println!("Requests: {}", requests.len());
    println!(
        "Normal evaluation: total {:?}, avg {:.2} us, allow count {}",
        normal_dur,
        micros_per_request(normal_dur, requests.len()),
        normal_allow
    );
    println!(
        "Cached PolTree:     total {:?}, avg {:.2} us, allow count {}",
        cached_dur,
        micros_per_request(cached_dur, requests.len()),
        cached_allow
    );
}
