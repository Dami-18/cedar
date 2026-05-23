use cedar_policy::{Authorizer, CachedAuthorizer, Entities, PolicySet, Request, Context, EntityUid, EntityId, EntityTypeName};
use std::str::FromStr;
use std::time::Instant;

fn main() {
    println!("=== Cedar Singleton Native Engine Simulator ===");

    // 1. Create a policy
    let s = r#"
        permit(
            principal == User::"alice",
            action == Action::"view",
            resource == Album::"trip"
        ) when {
            principal.age >= 18
        };
        
        permit(
            principal,
            action == Action::"edit",
            resource 
        ) when {
            principal == resource.owner
        };
    "#;
    
    let policy_set = PolicySet::from_str(s).expect("policy parsing failed");

    // 2. Create entities
    let e = r#"[
        {
            "uid": {"type":"User","id":"alice"},
            "attrs": {
                "age": 19
            },
            "parents": []
        },
        {
            "uid": {"type":"Action","id":"view"},
            "attrs": {},
            "parents": []
        },
        {
            "uid": {"type":"Album","id":"trip"},
            "attrs": {
                "owner": {"__entity": {"type": "User", "id": "alice"}}
            },
            "parents": []
        }
    ]"#;
    let entities = Entities::from_json_str(e, None).expect("entity parsing failed");

    // 3. Create a request
    let p_name = EntityTypeName::from_str("User").unwrap();
    let p_eid = EntityId::from_str("alice").unwrap();
    let principal = EntityUid::from_type_name_and_id(p_name, p_eid);

    let a_name = EntityTypeName::from_str("Action").unwrap();
    let a_eid = EntityId::from_str("view").unwrap();
    let action = EntityUid::from_type_name_and_id(a_name, a_eid);

    let r_name = EntityTypeName::from_str("Album").unwrap();
    let r_eid = EntityId::from_str("trip").unwrap();
    let resource = EntityUid::from_type_name_and_id(r_name, r_eid);

    let request = Request::new(principal, action, resource, Context::empty(), None).unwrap();

    let iterations = 100_000;
    println!("Benchmarking with {} iterations...", iterations);

    // --- Standard Authorizer Benchmark ---
    let std_authorizer = Authorizer::new();
    let start_std = Instant::now();
    for _ in 0..iterations {
        let _resp = std_authorizer.is_authorized(&request, &policy_set, &entities);
    }
    let duration_std = start_std.elapsed();
    println!("Standard Authorizer time: {:?}", duration_std);

    // --- Cached Authorizer Benchmark ---
    // Note: To be fair, `CachedAuthorizer` takes ownership, so we clone the set & entities
    let cached_authorizer = CachedAuthorizer::new(policy_set.clone(), entities.clone());
    
    // Explicit first call to trigger lazy initialization logic
    let start_cached_init = Instant::now();
    let _first_resp = cached_authorizer.is_authorized(&request);
    let duration_cached_init = start_cached_init.elapsed();
    println!("CachedAuthorizer Initial Compile (Lazy Init) time: {:?}", duration_cached_init);

    // Timing purely the cached executions
    let start_cached = Instant::now();
    for _ in 0..iterations {
        let _resp = cached_authorizer.is_authorized(&request);
    }
    let duration_cached = start_cached.elapsed();
    println!("CachedAuthorizer execution time:   {:?}", duration_cached);

    println!("--------------");
    let speedup = duration_std.as_secs_f64() / duration_cached.as_secs_f64();
    println!("Speedup ratio: {:.2}x", speedup);
}
