import tmp.sheaf.xif.paper.FlUnitsThetaPilotActionSourceActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource

-- Actual Kummer action data vs the F_l^x label action: compatibility/obstruction
--
-- Packages the actual vertical Kummer layer/arrow of
-- LogKummerCorrespondenceFromSource, and states the exact missing Kummer
-- label action homomorphism F_l^x -> Perm(SignedLabel) with compatibility.
-- A source action is constructed only conditionally from an explicit actual
-- homomorphism and compatibility hypothesis; no fake Kummer action is added.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotKummerActionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionSourceActual
open LeanFormal.IUT.XiFPaper.LogKummerCorrespondenceFromSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

-- Actual vertical Kummer layer at the core stage.
noncomputable def actualKummerLayerCore :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualVerticalKummerLayer (I := I) 0

-- Actual vertical Kummer arrow at the core stage.
noncomputable def actualKummerArrowCore :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualKummerArrow (I := I) 0

-- Actual vertical Kummer card of the 1-column log-Kummer correspondence.
noncomputable def actualKummerCardCore :
    SourceVerticalKummerCard (ActualKummerGroup (I := I)) I 1 :=
  actualVerticalKummerCard (I := I)

-- Exact missing Kummer label action: a homomorphism F_l^x -> Perm(SignedLabel)
-- induced by the actual Kummer data, with its Theta-pilot compatibility.
structure KummerThetaPilotLabelActionData where
  sourceAction : (Fl l.value)ˣ →* Equiv.Perm (SignedLabel l.value)
  kummer_compat : Prop

def KummerThetaPilotLabelActionObstruction : Prop :=
  Nonempty (KummerThetaPilotLabelActionData (l := l))

-- Conditional actual source-action data from an explicit Kummer label action
-- hom and its exact compatibility hypothesis.
noncomputable def flUnitsThetaPilotSourceActionOfKummer
    (rho : (Fl l.value)ˣ →* Equiv.Perm (SignedLabel l.value))
    (hcompat : Prop) :
    FlUnitsThetaPilotSourceActionData (l := l) where
  sourceAction := rho
  compat := hcompat

#check actualKummerLayerCore
#check actualKummerArrowCore
#check actualKummerCardCore
#check KummerThetaPilotLabelActionData
#check KummerThetaPilotLabelActionObstruction
#check flUnitsThetaPilotSourceActionOfKummer

end LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotKummerActionActual

end