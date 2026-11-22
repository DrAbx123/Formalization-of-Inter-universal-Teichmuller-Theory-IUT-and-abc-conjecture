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
  simp

end
end Probe2217
