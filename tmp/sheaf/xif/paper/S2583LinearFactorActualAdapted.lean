import tmp.sheaf.xif.paper.S2582P12ClosedActual
noncomputable section
set_option maxHeartbeats 16000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2583LinearFactorActualAdapted
open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S2582P12ClosedActual
theorem S2583_linearFactor : S2579LinearFactor613 := by
  refine ⟨(21 : ZMod 613), ?_⟩
  unfold S2579minpolyMod
  rw [S2582_P12Certificate]
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  unfold S2579P12
  decide
#print axioms S2583_linearFactor
end LeanFormal.IUT.XiFPaper.S2583LinearFactorActualAdapted
end
