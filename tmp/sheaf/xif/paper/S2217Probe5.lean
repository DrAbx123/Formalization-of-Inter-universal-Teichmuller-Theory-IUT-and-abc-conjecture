import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

namespace Probe2217
noncomputable section
set_option maxHeartbeats 2000000
attribute [local instance] Ideal.Quotient.field

theorem factorDegrees_X (k : Type) [Field k] :
    factorDegrees (X : k[X]) = ({1} : Multiset ℕ) := by
  unfold factorDegrees
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X)]
  rw [Monic.normalize_eq_self (monic_X)]
  simp

theorem rootCycleType_X_subsingleton
    (hsplit : ((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).Splits)
    (σ : Gal(ℚ/ℚ)) :
    rootCycleType ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ = 0 := by
  have hroot : ((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)) = (X : ℚ[X]) := by simp
  haveI : Subsingleton (((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).rootSet ℚ) := by
    rw [hroot]
    constructor
    intro a b
    apply Subtype.ext
    have ha : (a : ℚ) = 0 := by
      have h := a.2
      rw [mem_rootSet'] at h
      simpa using h.2
    have hb : (b : ℚ) = 0 := by
      have h := b.2
      rw [mem_rootSet'] at h
      simpa using h.2
    rw [ha, hb]
  unfold rootCycleType
  rw [Equiv.Perm.cycleType_eq_zero]
  ext x
  exact Subsingleton.elim _ _

example : ¬ DedekindFrobeniusCycleTypeTheorem := by
  intro h
  obtain ⟨p, hp⟩ := Ideal.exists_maximal (RingOfIntegers ℚ)
  haveI := hp
  have hmain := h ℚ ℚ (X : (RingOfIntegers ℚ)[X]) p p
    (monic_X) (by simpa using (separable_X (R := (RingOfIntegers ℚ) ⧸ p))) (by simp)
  obtain ⟨σ, -, hcyc⟩ := hmain
  have hfac : factorDegrees ((X : (RingOfIntegers ℚ)[X]).map (Ideal.Quotient.mk p)) = ({1} : Multiset ℕ) := by
    rw [show ((X : (RingOfIntegers ℚ)[X]).map (Ideal.Quotient.mk p)) = (X : ((RingOfIntegers ℚ) ⧸ p)[X]) by simp]
    exact factorDegrees_X _
  have hzero := rootCycleType_X_subsingleton (by simp) σ
  rw [hzero, hfac] at hcyc
  exact absurd hcyc (by simp)

end
end Probe2217
