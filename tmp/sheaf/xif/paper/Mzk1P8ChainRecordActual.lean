/- Record of the green P8 Frey-producer chain. -/
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVChainDoneActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ChainRecordActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVChainDoneActual
theorem p8ChainRecord_bound (h : ∀ ε : Real, 0 < ε → Nonempty (LeanFormal.IUT.XiFPaper.Mzk1G1Actual.FreyHeightBound ε)) :
    LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual.P8UniformHeightBound :=
  p8Chain_of_frey h
#print axioms p8ChainRecord_bound
end LeanFormal.IUT.XiFPaper.Mzk1P8ChainRecordActual
end
