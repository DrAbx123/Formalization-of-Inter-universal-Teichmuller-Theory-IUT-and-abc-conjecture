import tmp.sheaf.xif.paper.Mzk1PaperFaithful312NormedActual
import tmp.sheaf.xif.paper.Mzk1PaperFaithful312EvidenceRealActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual
import tmp.sheaf.xif.paper.SHEOutputAlignmentActual
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi concrete 3.12 assembly (A735)

Concrete construction of the IPL factorization from `sourceHaarActualOriginalInput`
and `actualIPLData`; `n=0`, `shift=0`, `source=ProcessionChoice.base`.
APT's `OriginalInput` over `FinitePlace k` and the SHE landing remain explicit
real source inputs (no constructor for them here). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FullConcreteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312EvidenceRealActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.APTComparisonFromSource
open LeanFormal.IUT.Theorem311Source.SHELandingActual
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.Theorem311Source.SourceUnitRegionHaarDataActual
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.SourceMultiradialPresentationWiring

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

variable {k : Type} [Field k] [NumberField k] {l' : PrimeGeFive}
variable (S : SourceDefinition31Data.{0} l')

/-- Concrete original input for the IPL side (`V = Unit`). -/
def concreteI : OriginalInput.{0, 0, 0, 0, 0} l' Unit :=
  sourceHaarActualOriginalInput (l := l') S

/-- Concrete IPL factorization from `actualIPLData`. -/
def concreteF :
    SourceLinkFactorization (ActualKummerGroup (I := concreteI S))
      (iplIntermediateStrip (I := concreteI S))
      (iplGauStrip (I := concreteI S))
      (iplEnvStrip (I := concreteI S))
      (iplCoricEnvStrip (I := concreteI S))
      (iplQPilotStrip (I := concreteI S)) :=
  (actualIPLData (I := concreteI S)).toLinkFactorization

/-- APT original input (over FinitePlace k) stays an explicit real source input. -/
variable (Iapt : OriginalInput.{0, 0, 0, 0, 0} l' (NumberField.FinitePlace k))
variable (landing : SHELandingForProcessionChoice (l := l') k)

noncomputable def cor312_full_concrete_contract : StepXIContract :=
  requirementContract (rpRequirementNorm T) (hqneg_norm T)
    (iplProp (concreteF S)) (ipl_proof (concreteF S))
    (sheProp T) (she_proof T)
    (aptProp Iapt 0 (0 : finiteLabel l') ProcessionChoice.base landing)
    (apt_proof Iapt 0 (0 : finiteLabel l') ProcessionChoice.base landing)

theorem cor312_full_concrete :
    Cor312Conclusion (cor312_full_concrete_contract T S Iapt landing) :=
  requirement_cor312 (rpRequirementNorm T) (hqneg_norm T)
    (iplProp (concreteF S)) (ipl_proof (concreteF S))
    (sheProp T) (she_proof T)
    (aptProp Iapt 0 (0 : finiteLabel l') ProcessionChoice.base landing)
    (apt_proof Iapt 0 (0 : finiteLabel l') ProcessionChoice.base landing)

end LeanFormal.IUT.XiFPaper.Mzk1Cor312FullConcreteActual

end
