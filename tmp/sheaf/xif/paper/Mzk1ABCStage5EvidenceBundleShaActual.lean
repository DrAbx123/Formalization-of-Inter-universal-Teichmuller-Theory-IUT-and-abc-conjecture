import tmp.sheaf.xif.paper.Mzk1Cor312AcceptedFinalActual
import tmp.sheaf.xif.paper.Mzk1Cor312ShaPaperEquivalenceActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-!
# A574 ABC Stage-5 EvidenceBundle (shehdd payload declarations, not log-only)

Bundles the resolved-acceptance facts into a single structure whose fields are
actual proofs (no `#print`-only gate, no True/sorry):
* signed/magnitude and strict equivalences;
* `C_Theta >= -1`;
* accepted signed/strict paper inequalities;
* non-vacuous xi-e requirement signed inequality.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5EvidenceBundleShaActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ShaPaperEquivalenceActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

structure ABCStage5EvidenceBundle where
  signed_iff : ∀ {qMag thetaMag : Real}, -thetaMag ≤ -qMag ↔ qMag ≤ thetaMag
  signed_strict_iff : ∀ {qMag thetaMag : Real}, -thetaMag < -qMag ↔ qMag < thetaMag
  ctheta_ge : ∀ {qMag C : Real}, 0 < qMag → -qMag ≤ C * qMag → -1 ≤ C
  ctheta_gt : ∀ {qMag C : Real}, 0 < qMag → -qMag < C * qMag → -1 < C
  accepted_signed : ∀ {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : PaperKummerReading T),
    R.qReading ≤ R.thetaReading
  accepted_strict : ∀ {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : PaperKummerReading T),
    R.qReading < R.thetaReading
  requirement_signed : ∀ {α : Type} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol),
    requirementSignedQ D ≤ requirementSignedTheta D

noncomputable def abcStage5EvidenceBundle : ABCStage5EvidenceBundle where
  signed_iff := fun {_ _} => signed_iff_magnitude
  signed_strict_iff := fun {_ _} => signed_strict_iff_magnitude
  ctheta_ge := fun {_ _} hq h => CTheta_of_signed hq h
  ctheta_gt := fun {_ _} hq h => CTheta_strict_of_signed hq h
  accepted_signed := fun T _ R => paperKummerReading_le T R
  accepted_strict := fun T _ R => paperKummerReading_strict T R
  requirement_signed := fun D => requirement_signed_inequality D

end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5EvidenceBundleShaActual
