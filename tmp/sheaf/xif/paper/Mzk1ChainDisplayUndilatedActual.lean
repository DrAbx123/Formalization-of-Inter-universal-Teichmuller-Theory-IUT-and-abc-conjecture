import tmp.sheaf.xif.paper.Mzk1E5DisplayInputsStatementActualV2
import tmp.sheaf.xif.paper.Mzk1E5UndilatedABCBridgeActualV2
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainDisplayUndilatedActual — display + undilated-interface ABC chain

Combines two EXIT0 consumers into a genuine new conclusion: the exact Thm 1.10
display from hCor312/hSlack holds together with ABCConjecture from the undilated
(b)+(c) bounds.  No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainDisplayUndilatedActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1E5DisplayInputsStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1E5UndilatedABCBridgeActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

universe u

/-- Display from hCor312/hSlack together with ABC from undilated (b)+(c). -/
theorem display_and_undilated_abc (T : Thm110DisplayTerms)
    (hcor : Cor312GapHyp T) (hslack : SlackHyp T)
    {X : Type u} {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    thm110Lhs T ≤ thm110Rhs T ∧ ABCConjecture :=
  ⟨final_display_of_inputs T ((displayInputs_iff T).mpr ⟨hcor, hslack⟩),
   abcConjecture_of_undilatedBounds hb hc⟩

/-- The display half alone, as a reusable projection of the chain. -/
theorem chain_display_of_gap_slack (T : Thm110DisplayTerms)
    (hcor : Cor312GapHyp T) (hslack : SlackHyp T) :
    thm110Lhs T ≤ thm110Rhs T :=
  final_display_of_inputs T ((displayInputs_iff T).mpr ⟨hcor, hslack⟩)

/-- The ABC half alone, as a reusable projection of the chain. -/
theorem chain_abc_of_undilated {X : Type u} {W : IQHullLogVolumeInterface X}
    {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    ABCConjecture :=
  abcConjecture_of_undilatedBounds hb hc

end LeanFormal.IUT.XiFPaper.Mzk1ChainDisplayUndilatedActual

end
