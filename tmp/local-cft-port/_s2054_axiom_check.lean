import ContinuousKummerTheory.Kummer.PAdic

open KummerTheory IsLocalRing

-- Axiom audit of every public declaration of Kummer.PAdic.
#print axioms KummerTheory.mem_pow_smul_top_iff
#print axioms KummerTheory.exists_fixedPoint_of_adicContraction
#print axioms KummerTheory.one_add_pow_eq
#print axioms KummerTheory.exists_pow_eq_one_add
#print axioms KummerTheory.finiteIndex_powRange_of_isDiscreteValuationRing
#print axioms KummerTheory.finiteKummerQuotients_of_isDiscreteValuationRing
#print axioms KummerTheory.kummerZHatEquivProfiniteCompletion
#print axioms KummerTheory.kummerCompletionEquivProfiniteCompletion
#print axioms KummerTheory.padicKummerZHatEquiv
#print axioms KummerTheory.instFiniteKummerQuotientsPadic

-- Statement / type locks
#check @KummerTheory.padicKummerZHatEquiv
#check @KummerTheory.finiteKummerQuotients_of_isDiscreteValuationRing
#check @KummerTheory.instFiniteKummerQuotientsPadic

-- Instance synthesis (consumer side)
example (p : ℕ) [Fact p.Prime] : FiniteKummerQuotients ℚ_[p] := inferInstance
example (p : ℕ) [Fact p.Prime] : Finite (IsLocalRing.ResidueField ℤ_[p]) := inferInstance
example (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] : FiniteKummerQuotients K := inferInstance
noncomputable example (p : ℕ) [Fact p.Prime] :
    ContH1 Gal(AlgebraicClosure ℚ_[p]/ℚ_[p]) (ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p])) ≃*
      ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of ℚ_[p]ˣ) :=
  padicKummerZHatEquiv p
