import proofs.PrivateClaimVerification

open Noctium Noctium.Verification

/-- "entrypoint":"claim","index":0,"mismatchedPolicyPairs":[],"missingRoles":[],"policyPairing":"matched","roles":[{"duplicateRegistrationCount":0,"registrations":[{"policy":"Noctium.PrivateClaimVerification.policy","proof":"Noctium.PrivateClaimVerification.functional"}],"role":"functional","status":"covered"},{"duplicateRegistrationCount":0,"registrations":[{"policy":"Noctium.PrivateClaimVerification.policy","proof":"Noctium.PrivateClaimVerification.privacy"}],"role":"privacy","status":"covered"}],"status":"covered" -/
#guard_msgs (substring := true) in
#noctium_source_proof_coverage PrivateClaim
