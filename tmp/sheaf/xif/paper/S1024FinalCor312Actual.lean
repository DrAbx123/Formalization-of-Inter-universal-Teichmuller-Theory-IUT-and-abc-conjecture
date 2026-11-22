import tmp.sheaf.xif.paper.S1018S995ReducedConditionsActual
import tmp.sheaf.xif.paper.S995FiniteCarrierCor312ConclusionActual
/-! # S1024: final Cor312 with actual S994FiniteInput
Openness is S1023 actual; S1018 constructs the S994FiniteInput.  The only
remaining conditions are sourceQ (hQ), the source link/hlink and finite links. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1024FinalCor312Actual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual
open LeanFormal.IUT.XiFPaper.S1018S995ReducedConditionsActual
open LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual
open LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual
open LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory
universe ua uv upi umon ui uL uC uG uX uLabel u uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
variable (C3 : SourcePilotRegionData (V := FinitePrimePlace 2 7) I)
theorem s1024FinalCor312
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (link : PaperXiFSourceLink O P C3)
    (hlink : link.link_identification)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
          (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
          P O C3 link hlink))).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((paperCertificate (I := paperXiFInput
        (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
          (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
          P O C3 link hlink))).toContract
        (paperSignedLinkEvidence
          (I := paperXiFInput
            (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
              (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
              P O C3 link hlink)) links)) :=
  s995Cor312Conclusion T P O C3 (s1018FiniteInput_actual T) link hlink links
end LeanFormal.IUT.XiFPaper.S1024FinalCor312Actual
