import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial NumberField
namespace Probe2217
noncomputable section
set_option maxHeartbeats 1000000

example (a : ℚ) : (a ∈ (X : (RingOfIntegers ℚ)[X]).rootSet ℚ) ↔ a = 0 := by
  rw [mem_rootSet']
  simp

example : (X : (RingOfIntegers ℚ)[X]).rootSet ℚ = {0} := by
  ext a
  rw [mem_rootSet']
  simp

#check Polynomial.rootSet_X
#check Polynomial.rootSet_X_sub_C

end
end Probe2217
