import tmp.sheaf.xif.paper.KummerLabelActionCompatibilityFullActualAdapted

-- Actual Kummer group action on SignedLabel: data/obstruction
--
-- The actual Kummer layer/arrow/card live on the actual Kummer group of the
-- core strip. Their image is the times-mu unit quotient; they do not provide
-- a homomorphism from the Kummer group to permutations of SignedLabel. This
-- file records the exact missing action and its compatibility with
-- flUnitsActionPerm; it does not fabricate one.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerArrowLabelActionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotKummerActionActual
open LeanFormal.IUT.XiFPaper.KummerThetaPilotLabelActionConstructionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

-- Actual Kummer group action data: a hom from the actual Kummer group to
-- permutations of the signed labels, with its compatibility proposition.
structure KummerGroupLabelActionData where
  action : ActualKummerGroup (I := I) →* Equiv.Perm (SignedLabel l.value)
  compatibility : Prop

def KummerGroupLabelActionObstruction : Prop :=
  Nonempty (KummerGroupLabelActionData (I := I))

-- Conditional actual action data from an explicit actual Kummer-group
-- homomorphism and exact compatibility hypothesis. No action is chosen.
noncomputable def kummerGroupLabelActionOfHom
    (rho : ActualKummerGroup (I := I) →* Equiv.Perm (SignedLabel l.value))
    (hcompat : Prop) :
    KummerGroupLabelActionData (I := I) where
  action := rho
  compatibility := hcompat

-- Actual Kummer data carried alongside the missing action.
noncomputable def actualKummerLayerForLabelAction :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualKummerLayerCore (I := I)

noncomputable def actualKummerArrowForLabelAction :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualKummerArrowCore (I := I)

noncomputable def actualKummerCardForLabelAction :
    SourceVerticalKummerCard (ActualKummerGroup (I := I)) I 1 :=
  actualKummerCardCore (I := I)

#check KummerGroupLabelActionData
#check KummerGroupLabelActionObstruction
#check kummerGroupLabelActionOfHom
#check actualKummerLayerForLabelAction
#check actualKummerArrowForLabelAction
#check actualKummerCardForLabelAction

end LeanFormal.IUT.XiFPaper.KummerArrowLabelActionActualAdapted

end