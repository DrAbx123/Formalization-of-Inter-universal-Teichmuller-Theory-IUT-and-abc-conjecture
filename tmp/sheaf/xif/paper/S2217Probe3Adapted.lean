import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

namespace Probe2217
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Ideal.Quotient.field

example (p : Ideal (RingOfIntegers ℚ)) [p.IsMaximal] :
    factorDegrees ((X : (RingOfIntegers ℚ)[X]).map (Ideal.Quotient.mk p)) = ({1} : Multiset ℕ) := by
  unfold factorDegrees
  rw [show ((X : (RingOfIntegers ℚ)[X]).map (Ideal.Quotient.mk p)) = (X : ((RingOfIntegers ℚ) ⧸ p)[X]) by simp]
  rw [normalizedFactors_irreducible (irreducible_X)]
  simp

example : Subsingleton ((X : (RingOfIntegers ℚ)[X]).rootSet ℚ) := by
  constructor
  intro a b
  apply Subtype.ext
  have ha : (a : ℚ) = 0 := by
    simpa using a.2
  have hb : (b : ℚ) = 0 := by
    simpa using b.2
  rw [ha, hb]

example (σ : Gal(ℚ/ℚ)) (hsplit : ((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).Splits) :
    rootCycleType ℚ ℚ (X : (RingOfIntegers ℚ)[X]) hsplit σ = 0 := by
  unfold rootCycleType
  haveI : Subsingleton (((X : (RingOfIntegers ℚ)[X]).map (algebraMap (RingOfIntegers ℚ) ℚ)).rootSet ℚ) := by
    convert (inferInstance : Subsingleton ((X : (RingOfIntegers ℚ)[X]).rootSet ℚ)) using 1
    simp
  rw [Equiv.Perm.cycleType_eq_zero]
  ext x
  exact Subsingleton.elim _ _

end
end Probe2217
