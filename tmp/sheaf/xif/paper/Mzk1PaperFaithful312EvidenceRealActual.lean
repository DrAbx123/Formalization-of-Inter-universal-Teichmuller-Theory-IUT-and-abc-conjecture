import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.APTComparisonFromSource
import tmp.sheaf.xif.paper.IPLAPTActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi paper-faithful 3.12 evidence (A726/A728)

No `structure ... : Prop` wrapper, no arbitrary ipl/she/apt props.
* SHE: `kummerMap_thetaOne T`;
* IPL: actual `SourceLinkFactorization` frozen formula (parametric in the actual data);
* APT: actual `SourceAPTStatement` from `actualAPTStatement_of_landing`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312EvidenceRealActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.APTComparisonFromSource
open LeanFormal.IUT.Theorem311Source.SHELandingActual
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.SourceMultiradialPresentationWiring

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

def sheProp (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  kummerMap T (thetaOneCarrier T) = qPilotInThetaCarrier T

theorem she_proof (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : sheProp T :=
  kummerMap_thetaOne T

section IPL

variable {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}

def iplProp (F : SourceLinkFactorization G intermediateStrip gauStrip envStrip
    coricEnvStrip qPilotStrip) : Prop :=
  F.inputLink = F.composite

theorem ipl_proof (F : SourceLinkFactorization G intermediateStrip gauStrip envStrip
    coricEnvStrip qPilotStrip) : iplProp F :=
  F.factorization

end IPL

variable {k : Type} [Field k] [NumberField k] {l' : PrimeGeFive}
variable {n : Int} {shift : finiteLabel l'} {source : ProcessionChoice l'}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l' (NumberField.FinitePlace k)}

def aptProp (I : OriginalInput.{0, 0, 0, 0, 0} l' (NumberField.FinitePlace k))
    (n : Int) (shift : finiteLabel l') (source : ProcessionChoice l')
    (landing : SourceLocalizationExpressible
      (oneColumnStructure (k := k)) (ProcessionChoice l')) : Prop :=
  SourceAPTStatement (oneColumnStructure (k := k))
    (finiteKernelSourceAlgorithm l' I n (finiteKernelComparisonInput l' source))
    (finiteKernelSourceAlgorithm l' I (n + 1)
      (finiteKernelComparisonInput l' (ProcessionChoice.ind2Act shift source)))

theorem apt_proof (I : OriginalInput.{0, 0, 0, 0, 0} l' (NumberField.FinitePlace k))
    (n : Int) (shift : finiteLabel l') (source : ProcessionChoice l')
    (landing : SourceLocalizationExpressible
      (oneColumnStructure (k := k)) (ProcessionChoice l')) :
    aptProp I n shift source landing :=
  actualAPTStatement_of_landing I n shift source landing

noncomputable def faithfulContract {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
    (F : SourceLinkFactorization G intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip)
    (I : OriginalInput.{0, 0, 0, 0, 0} l' (NumberField.FinitePlace k))
    (n : Int) (shift : finiteLabel l') (source : ProcessionChoice l')
    (landing : SourceLocalizationExpressible
      (oneColumnStructure (k := k)) (ProcessionChoice l')) :
    StepXIContract :=
  requirementContract D hqneg (iplProp F) (ipl_proof F)
    (sheProp T) (she_proof T) (aptProp I n shift source landing)
    (apt_proof I n shift source landing)

theorem faithful_cor312 {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
    (F : SourceLinkFactorization G intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip)
    (I : OriginalInput.{0, 0, 0, 0, 0} l' (NumberField.FinitePlace k))
    (n : Int) (shift : finiteLabel l') (source : ProcessionChoice l')
    (landing : SourceLocalizationExpressible
      (oneColumnStructure (k := k)) (ProcessionChoice l')) :
    Cor312Conclusion
      (faithfulContract T D hqneg F I n shift source landing) :=
  requirement_cor312 D hqneg (iplProp F) (ipl_proof F)
    (sheProp T) (she_proof T) (aptProp I n shift source landing)
    (apt_proof I n shift source landing)

end LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312EvidenceRealActual

end
