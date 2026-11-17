import Nightlean.Verification.ScalarCache

namespace ScalarCacheTests

open Nightlean Nightlean.Backend Nightlean.Verification NativeRelation ScalarLowering ScalarCache

/-- A cached hash key must point to the exact literal field domain. Operand
decoding alone does not permit substituting an arbitrary domain operand. -/
example (domain : Nat) (wrong : Scalar) (left right : Operand) (a b output : String)
    (different : wrong ≠ scalar domain) :
    ¬ CacheCorresponds ("transient_hash", [a, b], some domain) output
      (.hash [.immediate wrong, left, right] output) := by
  intro correspondence
  rcases correspondence with ⟨_, foundDomain, foundA, foundB, domainText, foundLeft, foundRight,
    keyEq, valuesEq, _, _, _, _⟩
  cases keyEq
  simp only [List.cons.injEq, Operand.immediate.injEq] at valuesEq
  exact different valuesEq.1

example (left right output : String) (a b : Operand) :
    ¬ CacheCorresponds ("test_eq", [left, right], none) output (.mul a b output) := by
  simp [CacheCorresponds]

#print axioms Nightlean.Verification.ScalarCache.cached_testEq_meaning
#print axioms Nightlean.Verification.ScalarCache.cached_neg_meaning
#print axioms Nightlean.Verification.ScalarCache.cached_not_meaning
#print axioms Nightlean.Verification.ScalarCache.cached_select_meaning
#print axioms Nightlean.Verification.ScalarCache.cached_hash_meaning

end ScalarCacheTests
