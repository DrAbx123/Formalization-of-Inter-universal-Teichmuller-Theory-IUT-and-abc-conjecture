import tmp.sheaf.xif.paper.Mzk1PaperFaithful312NormedActual
import tmp.sheaf.xif.paper.Mzk1PaperFaithful312EvidenceRealActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

/-!
# stepxi full 3.12 assembly with normalized hqneg + real IPL/SHE/APT

Uses mainline's green `rpRequirementNorm`/`hqneg_norm` and stepxi's real
`iplProp`/`sheProp`/`aptProp`; no arbitrary qualitative Prop. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICor312FullAssemblyActual

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
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.SourceMultiradialPresentationWiring

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

noncomputable def cor312_full_contract
    {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
    (F : SourceLinkFactorization G intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip)
    {k : Type} [Field k] [NumberField k] {l' : PrimeGeFive}
    {n : Int} {shift : finiteLabel l'} {source : ProcessionChoice l'}
    (I : OriginalInput.{0, 0, 0, 0, 0} l' (NumberField.FinitePlace k))
    (landing : SourceLocalizationExpressible
      (oneColumnStructure (k := k)) (ProcessionChoice l')) :
    StepXIContract :=
  requirementContract (rpRequirementNorm T) (hqneg_norm T)
    (iplProp F) (ipl_proof F) (sheProp T) (she_proof T)
    (aptProp I n shift source landing) (apt_proof I n shift source landing)

theorem cor312_full
    {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
    (F : SourceLinkFactorization G intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip)
    {k : Type} [Field k] [NumberField k] {l' : PrimeGeFive}
    {n : Int} {shift : finiteLabel l'} {source : ProcessionChoice l'}
    (I : OriginalInput.{0, 0, 0, 0, 0} l' (NumberField.FinitePlace k))
    (landing : SourceLocalizationExpressible
      (oneColumnStructure (k := k)) (ProcessionChoice l')) :
    Cor312Conclusion
      (cor312_full_contract (n := n) (shift := shift) (source := source) T F I landing) :=
  requirement_cor312 (rpRequirementNorm T) (hqneg_norm T)
    (iplProp F) (ipl_proof F) (sheProp T) (she_proof T)
    (aptProp I n shift source landing) (apt_proof I n shift source landing)

end LeanFormal.IUT.XiFPaper.Mzk1StepXICor312FullAssemblyActual

end
