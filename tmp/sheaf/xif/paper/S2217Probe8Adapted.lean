import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

namespace Probe2217
noncomputable section
set_option maxHeartbeats 2000000
attribute [local instance] Ideal.Quotient.field

example (a : ℚ) : a ∈ ((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).rootSet ℚ ↔ a = 0 := by
  rw [mem_rootSet']
  simp

example : Subsingleton (((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).rootSet ℚ) := by
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

example (σ : Gal(ℚ/ℚ))
    (hsplit : ((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).Splits) :
    rootCycleType ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ = 0 := by
  haveI : Subsingleton (((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).rootSet ℚ) := by
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
  have hperm : rootPerm ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ = 1 := by
    ext x
    exact Subsingleton.elim _ _
  unfold rootCycleType
  rw [hperm, Equiv.Perm.cycleType_one]

end
end Probe2217
