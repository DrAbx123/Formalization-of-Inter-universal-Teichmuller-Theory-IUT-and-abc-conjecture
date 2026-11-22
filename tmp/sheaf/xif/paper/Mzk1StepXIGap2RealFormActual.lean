import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import tmp.sheaf.xif.paper.A502HcompToRealAdapterActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap-2 real/ENNReal equivalence (real content)

The named ENNReal-form Gap-2 estimate is equivalent to the paper real-form
inequality under finiteness and nonnegativity. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2RealFormActual

open LeanFormal.IUT.Objects.ABCBridgeGap2

theorem gap2_real_iff {regionVolume : ENNReal} {eps weight theta D : Real}
    (hfin : regionVolume ≠ ⊤)
    (hR : 0 ≤ (1 + eps) * weight + theta + D) :
    SNamed regionVolume eps weight theta D ↔
      regionVolume.toReal ≤ (1 + eps) * weight + theta + D :=
  ⟨fun hS => gap2_real_bound hR hS,
    fun h => gap2_ennreal_bound hfin hR h⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2RealFormActual

end
