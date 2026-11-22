import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

namespace Probe2217
noncomputable section
set_option maxHeartbeats 2000000
attribute [local instance] Ideal.Quotient.field

example (p : Ideal (RingOfIntegers ℚ)) : p.LiesOver p := by
  refine ⟨?_⟩
  show p = Ideal.comap (algebraMap (RingOfIntegers ℚ) (RingOfIntegers ℚ)) p
  simp

example (k : Type) [Field k] : factorDegrees (X : k[X]) = ({1} : Multiset ℕ) := by
  classical
  unfold factorDegrees
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X)]
  rw [Monic.normalize_eq_self (monic_X)]
  simp

end
end Probe2217
