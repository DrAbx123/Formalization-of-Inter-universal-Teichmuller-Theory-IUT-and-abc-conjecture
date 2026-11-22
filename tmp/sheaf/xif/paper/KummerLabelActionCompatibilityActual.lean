import tmp.sheaf.xif.paper.KummerThetaPilotLabelActionConstructionActual

-- Kummer label-action compatibility: actual unit-level evidence + exact
-- full compatibility obstruction
--
-- The actual Kummer layer/arrow and the actual algebraic label action are
-- available. Their full compatibility is not constructed; the exact required
-- proposition is recorded below. Only the unit-level compatibility follows
-- from the actual monoid laws and is proved. No fake full compatibility.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerLabelActionCompatibilityActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionSourceActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotKummerActionActual
open LeanFormal.IUT.XiFPaper.KummerThetaPilotLabelActionConstructionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V)

-- Actual unit-level compatibility: the actual algebraic label action at 1 is
-- the identity Theta-pilot action, by the actual monoid laws.
theorem actualKummerLabelAction_unit_compat :
    sourceThetaPilotActionOfPerm (I := I) v (actualKummerLabelActionHom (l := l)) 1 =
      id := by
  ext x p
  rfl

-- Exact obstruction: an inhabitant of the Kummer label-action compatibility
-- structure (from the construction layer) is the precise missing object.
def KummerLabelActionCompatibilityObstruction : Prop :=
  Nonempty (KummerLabelActionCompatibility (I := I))

#check actualKummerLabelAction_unit_compat
#check KummerLabelActionCompatibilityObstruction

end LeanFormal.IUT.XiFPaper.KummerLabelActionCompatibilityActual

end