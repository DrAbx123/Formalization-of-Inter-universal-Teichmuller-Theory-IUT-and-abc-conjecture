import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

namespace Probe2217
noncomputable section
set_option maxHeartbeats 2000000
attribute [local instance] Ideal.Quotient.field

theorem factorDegrees_X (k : Type) [Field k] :
    factorDegrees (X : k[X]) = ({1} : Multiset ℕ) := by
  classical
  unfold factorDegrees
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X)]
  rw [Monic.normalize_eq_self (monic_X)]
  simp

theorem rootCycleType_X (hsplit : ((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).Splits)
    (σ : Gal(ℚ/ℚ)) :
    rootCycleType ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ =
      (rootPerm ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ).cycleType := by
  simp only [rootCycleType]

example : ¬ DedekindFrobeniusCycleTypeTheorem := by
  classical
  intro h
  obtain ⟨p, hp⟩ := Ideal.exists_maximal (RingOfIntegers ℚ)
  letI : p.IsMaximal := hp
  letI : Algebra (RingOfIntegers ℚ) (RingOfIntegers ℚ) := Algebra.id _
  haveI : p.LiesOver p := ⟨by simp⟩
  have hsplit : ((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).Splits := by simp
  have hmain := h ℚ ℚ (X : (RingOfIntegers ℚ)[X]) p p
    (monic_X) (by simpa using (separable_X (R := (RingOfIntegers ℚ) ⧸ p))) hsplit
  obtain ⟨σ, -, hcyc⟩ := hmain
  have hfac : factorDegrees ((X : (RingOfIntegers ℚ)[X]).map (Ideal.Quotient.mk p)) = ({1} : Multiset ℕ) := by
    rw [show ((X : (RingOfIntegers ℚ)[X]).map (Ideal.Quotient.mk p)) = (X : ((RingOfIntegers ℚ) ⧸ p)[X]) by simp]
    exact factorDegrees_X _
  have hmem : (1 : ℕ) ∈ rootCycleType ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ := by
    rw [hcyc, hfac]
    simp
  rw [rootCycleType_X] at hmem
  have hlt : 1 < 1 := Equiv.Perm.one_lt_of_mem_cycleType (σ := rootPerm ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ) hmem
  exact lt_irrefl 1 hlt

end
end Probe2217
