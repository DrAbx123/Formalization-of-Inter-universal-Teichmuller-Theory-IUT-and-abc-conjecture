/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A736: audit of lana's ABC statements vs our ABCConjecture (read-only) -/

/- Sources:
* lana: tmp/online/lana-agents__iut/iut-main/Iut/Abc/Classical.lean:38 `ClassicalABC`;
  Iut/Concrete/ThetaRegion.lean:375 `Cor312VariantHolds`;
  Iut/Tripod/Main.lean:120 `abc_of_variant` (Cor312VariantHolds -> tripodTheory.StatementII);
  Iut/Tripod/ClassicalAbc.lean:286 `classicalABC_of_statementI` (StatementI -> ClassicalABC
  via `classicalABCInt_of_statementI` and `classicalABC_of_int`).
* ours: LeanFormal/IUT/ABCBridge/Statement.lean:32 `ABCConjecture`,
  `ABCInequality` (:28), `radical := natRadical` (:24), `IsABCTriple := PrimitiveAdditiveTriple` (:26).

## Exact lana form (Classical.lean:38-40)
`ClassicalABC := forall eps>0, exists C:Real, forall a b c:Nat, 0<a -> 0<b ->
   Nat.Coprime a b -> a+b=c -> (c:Real) <= C * ((radical (a*b*c):Nat):Real)^(1+eps)`
where `radical` is Mathlib's (UniqueFactorizationMonoid) radical on Nat.  No logarithm;
height is `c` itself; coprimality is stated as `Nat.Coprime a b` (equivalent to the
pairwise form given `a+b=c`).

## Exact our form (Statement.lean:28-35)
`ABCInequality eps K a b c := (c:Real) <= K * Real.rpow ((radical (a*b*c):Nat):Real) (1+eps)`;
`ABCConjecture := forall eps>0, exists K>0, forall a b c:Nat, IsABCTriple a b c ->
   ABCInequality eps K a b c`, with `radical := natRadical` and
`IsABCTriple := PrimitiveAdditiveTriple` (positivity/coprimality/a+b=c packaged).

## Differences and required bridge lemmas
1. radical dictionary: `natRadical (n) = UniqueFactorizationMonoid.radical n` on Nat
   (both = product of distinct prime divisors; our `radical` is an abbrev of natRadical).
2. triple dictionary: `IsABCTriple a b c <-> (0<a and 0<b and Nat.Coprime a b and a+b=c)`
   (PrimitiveAdditiveTriple decomposition; note lana omits explicit 0<c since c=a+b).
3. exponent form: lana writes `x^(1+eps)` on Real; our inequality uses `Real.rpow x (1+eps)`;
   need `x ^ (1+eps : Real) = Real.rpow x (1+eps)` (or unify to rpow; in lana `^` is
   Mathlib rpow notation on Real).
4. constant positivity: ours requires `K>0`; lana's `C` arbitrary, so need the standard
   `exists C>0` normalization lemma (`C' := max C 1`).
5. quantifier order/shape otherwise identical (eps -> C -> triples; multiplicative,
   no log-height).  In particular our ABCConjecture is NOT the logarithmic Wyx form; it
   matches ClassicalABC shape directly, so the bridge is at the dictionary level (1-4).

## Cor 3.12 variant side (lana)
`Cor312VariantHolds := forall D : InitialThetaData, Corollary312Variant
   (concreteVariantData D)` (ThetaRegion.lean:375) — i.e. `-|log q| <= -|log Theta|` for
the concrete variant data; `abc_of_variant` (Main.lean:120) turns it into
`tripodTheory.StatementII`, and `classicalABC_of_statementI`/`classicalABC_of_int` close the
chain to ClassicalABC.  Our bridge chain (Cor312Conclusion -> ABC) is separate; audit only.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1AbcBridgeAuditActual

/-- Audit rows: (aspect, lana side, our side, required bridge lemma). -/
def abcBridgeAuditRows : List (String × String × String × String) :=
  [ ("statement shape", "eps->C->triples, c <= C*rad^(1+eps)",
     "eps->K>0->triples, c <= K*rpow(rad)(1+eps)",
     "ABCInequality unification + constant positivity normalization"),
    ("radical", "Mathlib UniqueFactorizationMonoid.radical on Nat",
     "our radical := natRadical", "natRadical_eq_radical lemma"),
    ("triple predicate", "0<a, 0<b, Nat.Coprime a b, a+b=c",
     "IsABCTriple := PrimitiveAdditiveTriple", "PrimitiveAdditiveTriple decomposition iff"),
    ("exponent", "Real power x^(1+eps)", "Real.rpow x (1+eps)",
     "rpow/pow notation unification"),
    ("Cor312 variant", "Cor312VariantHolds := forall D, Corollary312Variant (concreteVariantData D)",
     "Cor312Conclusion (StepXI contract)", "separate chain; not bridged in this audit") ]

theorem abcBridgeAuditRows_length : abcBridgeAuditRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1AbcBridgeAuditActual
