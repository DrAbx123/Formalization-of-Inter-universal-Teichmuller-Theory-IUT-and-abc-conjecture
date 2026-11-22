import tmp.sheaf.xif.paper.KummerArrowLabelActionActual

-- Kummer group structure: actual unit action + exact label-action obstruction
--
-- ActualKummerGroup is the actual product group of the core strip. Its actual
-- Kummer-card action is on the times-mu unit quotients, not on SignedLabel.
-- This file records that actual unit action and the exact missing label-action
-- homomorphism; no label action is fabricated. WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerGroupLabelActionFromCardActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotKummerActionActual
open LeanFormal.IUT.XiFPaper.KummerThetaPilotLabelActionConstructionActual
open LeanFormal.IUT.XiFPaper.KummerArrowLabelActionActual
open LeanFormal.IUT.XiFPaper.LogKummerCorrespondenceFromSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

-- The actual group action of ActualKummerGroup on the times-mu unit
-- quotients of the core strip, from the actual Kummer layer.
noncomputable def actualKummerGroupActionOnUnits (v : V) :
    ActualKummerGroup (I := I) →*
      MulAut (TimesMuQuotient ((I.fPrimeStripAt 1 0).Mon v)ˣ) :=
  TimesMuQuotient.action ((actualKummerLayerCore (I := I)).sourceAction v)

-- The actual Kummer arrow's strip isomorphism is a real F-prime-strip
-- equivalence (not a label permutation).
def actualKummerArrowStripIso :
    FPrimeStripEquiv (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  (actualKummerArrowCore (I := I)).stripIso

-- Exact missing label action: an actual homomorphism from ActualKummerGroup
-- to permutations of SignedLabel, with compatibility. The actual card action
-- above is on times-mu units, so this is not derived here.
structure KummerGroupLabelActionRequired where
  action : ActualKummerGroup (I := I) →* Equiv.Perm (SignedLabel l.value)
  compatibility : Prop

def KummerGroupLabelActionRequiredObstruction : Prop :=
  Nonempty (KummerGroupLabelActionRequired (I := I))

#check actualKummerGroupActionOnUnits
#check actualKummerArrowStripIso
#check KummerGroupLabelActionRequired
#check KummerGroupLabelActionRequiredObstruction

end LeanFormal.IUT.XiFPaper.KummerGroupLabelActionFromCardActual

end