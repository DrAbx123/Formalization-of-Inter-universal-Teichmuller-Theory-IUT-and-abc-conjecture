import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptedFinalActual
import tmp.sheaf.xif.paper.Mzk1S1902LogVolumeInstanceActual

/-!
# A588 resolved-requirement acceptance (shehdd)

Acceptance bundle for the xi-e requirement with `strict_measure` and the
signed comparison treated as actual theorems/data:
* strict/weak signed requirement inequalities (actual proofs);
* `Cor312Conclusion` from the requirement contract with real IPL/SHE/APT data;
* accepted paper signed/strict inequalities and `C_Theta` form;
* S1902 real log-volume normalization (`s1902VolReal unitRegion = 1`), the
  partial-instance volume side of the resolved requirement.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementAcceptanceShaActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902LogVolumeInstanceActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory

universe u

structure ResolvedRequirementAcceptance where
  requirement_strict : ∀ {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol),
    requirementSignedQ D < requirementSignedTheta D
  requirement_weak : ∀ {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol),
    requirementSignedQ D ≤ requirementSignedTheta D
  requirement_cor312 : ∀ {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt),
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt)
  accepted_signed : ∀ {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : PaperKummerReading T),
    R.qReading ≤ R.thetaReading
  accepted_strict : ∀ {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : PaperKummerReading T),
    R.qReading < R.thetaReading
  s1902_unitRegion_norm : ∀ {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))],
    s1902VolReal T (s1902UnitRegion T) = 1

noncomputable def resolvedRequirementAcceptance : ResolvedRequirementAcceptance where
  requirement_strict := fun D => requirement_strict_signed D
  requirement_weak := fun D => requirement_signed_inequality D
  requirement_cor312 := fun D hqneg ipl hipl she hshe apt hapt =>
    requirement_cor312 D hqneg ipl hipl she hshe apt hapt
  accepted_signed := fun T _ R => paperKummerReading_le T R
  accepted_strict := fun T _ R => paperKummerReading_strict T R
  s1902_unitRegion_norm := fun T _ => s1902VolReal_unitRegion T

end LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementAcceptanceShaActual
