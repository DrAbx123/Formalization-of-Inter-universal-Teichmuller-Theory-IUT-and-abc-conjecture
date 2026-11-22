import tmp.sheaf.xif.paper.KummerLabelActionCompatibilityActualAdapted

-- Full Kummer-to-label action compatibility: actual algebraic identity plus
-- exact Kummer obstruction
--
-- The algebraic source action constructed from flUnitsActionPerm is literally
-- IndeterminaciesActual.labelPerm (flUnitsActionPerm u); this equality is
-- proved for every unit u. The Kummer side has no actual homomorphism to
-- label permutations, so the full Kummer compatibility remains the exact
-- obstruction, not a fake proof. WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerLabelActionCompatibilityFullActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionSourceActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotKummerActionActual
open LeanFormal.IUT.XiFPaper.KummerThetaPilotLabelActionConstructionActual
open LeanFormal.IUT.XiFPaper.KummerLabelActionCompatibilityActualAdapted

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V)

-- Actual identity for every unit: the constructed algebraic Theta-pilot action
-- is exactly IndeterminaciesActual.labelPerm applied to flUnitsActionPerm u.
theorem algebraicKummerLabelAction_eq_labelPerm (u : (Fl l.value)ˣ) :
    sourceThetaPilotActionOfPerm (I := I) v
        (actualKummerLabelActionHom (l := l)) u =
      I.labelPerm v (flUnitsActionPerm (l := l) u) := rfl

-- Actual identity of the underlying label permutations at all u.
theorem algebraicKummerLabelPerm_eq (u : (Fl l.value)ˣ) :
    actualKummerLabelActionHom (l := l) u = flUnitsActionPerm (l := l) u := rfl

-- Exact full Kummer compatibility obstruction: an actual inhabitant of the
-- KummerLabelActionCompatibility structure (Kummer layer/arrow plus the
-- algebraic permAction and compatibility proposition) is the precise missing
-- object. The algebraic identities above do not identify the Kummer action.
def KummerLabelActionFullCompatibilityObstruction : Prop :=
  Nonempty (KummerLabelActionCompatibility (I := I))

#check algebraicKummerLabelAction_eq_labelPerm
#check algebraicKummerLabelPerm_eq
#check KummerLabelActionFullCompatibilityObstruction

end LeanFormal.IUT.XiFPaper.KummerLabelActionCompatibilityFullActualAdapted

end