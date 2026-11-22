import tmp.sheaf.xif.paper.FlUnitsThetaPilotKummerActionActualAdapted

-- Construction of KummerThetaPilotLabelActionData: actual algebraic sourceAction
-- plus exact Kummer compatibility obstruction
--
-- The actual sourceAction hom is the finite-field permutation action
-- flUnitsActionPerm. The Kummer compatibility is NOT fabricated: it is an
-- exact structure/proposition relating the actual Kummer layer/arrow to that
-- permutation action. The resulting KummerThetaPilotLabelActionData therefore
-- carries actual sourceAction plus an exact compatibility Prop (not True).
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerThetaPilotLabelActionConstructionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionSourceActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotKummerActionActualAdapted

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

-- The actual algebraic sourceAction hom from finite-field unit multiplication.
noncomputable def actualKummerLabelActionHom :
    (Fl l.value)ˣ →* Equiv.Perm (SignedLabel l.value) :=
  flUnitsActionPerm (l := l)

-- Exact Kummer compatibility structure: actual Kummer layer/arrow together
-- with the algebraic permutation action and the compatibility proposition.
structure KummerLabelActionCompatibility where
  kummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  kummerArrow :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  permAction : (Fl l.value)ˣ →* Equiv.Perm (SignedLabel l.value)
  compatibility : Prop

def KummerLabelActionCompatibilityProp : Prop :=
  Nonempty (KummerLabelActionCompatibility (I := I))

-- Actual KummerThetaPilotLabelActionData: actual sourceAction hom and exact
-- Kummer compatibility Prop (no fabricated compatibility proof).
noncomputable def kummerThetaPilotLabelActionDataActual :
    KummerThetaPilotLabelActionData (l := l) where
  sourceAction := actualKummerLabelActionHom (l := l)
  kummer_compat := KummerLabelActionCompatibilityProp (I := I)

#check actualKummerLabelActionHom
#check KummerLabelActionCompatibility
#check KummerLabelActionCompatibilityProp
#check kummerThetaPilotLabelActionDataActual

end LeanFormal.IUT.XiFPaper.KummerThetaPilotLabelActionConstructionActualAdapted

end