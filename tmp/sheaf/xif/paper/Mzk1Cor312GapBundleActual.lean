import tmp.sheaf.xif.paper.Mzk1Cor312StatementShapeActual
import tmp.sheaf.xif.paper.Mzk1G2EGapInputsActual

/-! Mainline: composition of Cor 3.12 statement shape (via S2717 upper gap) with the
  ABC conclusion from G2.e gap inputs (new conjunction). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312GapBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementShapeActual
open LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsActual

universe u

theorem cor312_and_abc_of_upperGap_and_gapInputs
    (h : LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual.S2717UpperGap)
    {X : Type u} {W : IQHullLogVolumeInterface X}
    (logShellPoint : Nat → Nat → Nat → X)
    (I : ∀ epsilon : Real, 0 < epsilon → EpsilonGapInputs W logShellPoint epsilon) :
    Cor312StatementShape ∧ ABCConjecture :=
  ⟨cor312Statement_of_upperGap h, abcConjecture_of_gapInputs X W logShellPoint I⟩

end LeanFormal.IUT.XiFPaper.Mzk1Cor312GapBundleActual