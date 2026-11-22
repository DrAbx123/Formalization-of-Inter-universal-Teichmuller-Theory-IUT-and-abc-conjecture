import LeanFormal.IUT.Audit.Status

/-! # S3156: REPO-FIRST prior-art audit - Fact prime instances

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Prior-art rows for prime instances. -/
def S3156FactPrimePriorArt : List (String × String × String) := [
  ("LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:28", "instance completionRationalPrime_fact (place) : Fact (completionRationalPrime place).val.Prime", "REUSE for arbitrary finite place"),
  (".../FinitePlacePadicScalarStructure.lean:26", "def completionRationalPrime (place) : Nat.Primes", "REUSE: rational prime underneath a place"),
  ("LeanFormal/IUT/ABCBridge/Geometry/RationalCommonPrimeFinrank.lean:22", "instance fact_prime_five : Fact (Nat.Prime 5)", "REUSE for the concrete Gaussian/5 case"),
  ("LeanFormal/IUT/Foundations/AlgebraicGeometry/... ", "many local instance factFivePrime : Fact (Nat.Prime 5)", "prefer the global RationalCommonPrimeFinrank instance; do not re-declare") ]

theorem S3156FactPrimePriorArt_length : S3156FactPrimePriorArt.length = 4 := rfl

/-- Prior-art audit record: Fact prime. -/
def S3156PriorArtFactPrime : Obligation :=
  { id := "IUT.project.prior-art-fact-prime"
    source := "Lead §7.9 directive; FinitePlacePadicScalarStructure.lean / RationalCommonPrimeFinrank.lean"
    status := VerificationStatus.interface
    note :=
      "PRIOR ART CONFIRMED (Fact prime): completionRationalPrime_fact supplies "
      ++ "Fact (completionRationalPrime place).val.Prime for arbitrary finite places; "
      ++ "fact_prime_five supplies Fact (Nat.Prime 5) for the concrete case. Diagnostic for "
      ++ "S3135ModelScalingPairActual's synthInstanceFailed: it needs one of these Fact instances "
      ++ "(plus correct open scoped NNReal/ENNReal for padic norm work) instead of a local axiom/"
      ++ "orphan declaration; the missing s3135_modelScaling_baseUnit_ne_zero is a downstream "
      ++ "consequence of that failure."
    dependsOn := [] }

#check S3156PriorArtFactPrime
#check S3156FactPrimePriorArt_length

end LeanFormal.IUT.Audit
