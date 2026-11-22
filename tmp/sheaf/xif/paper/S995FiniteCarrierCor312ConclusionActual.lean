import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual
import tmp.sheaf.xif.paper.S979TensorRegionHullInequalityActual
/-! # S995: final finite-carrier Cor312Conclusion
Combines S994 per-b/global finite-carrier inequalities and a PaperXiFSourceLink
with finite links, then calls paperAssembly_cor312Conclusion.  Only
S994FiniteInput + hQ/hC3 (through the supplied link) + finite links; no equality
or scaling data. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual
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
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual
open LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual
open LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual
open MeasureTheory
universe ua uv upi umon ui uL uC uG uW uX uLabel u uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
variable (C3 : SourcePilotRegionData (V := FinitePrimePlace 2 7) I)
/-- Final finite-carrier Cor312Conclusion. -/
theorem s995FiniteCarrierCor312Conclusion
    (In : S994FiniteInput T)
    (link : PaperXiFSourceLink O P C3)
    (hlink : link.link_identification)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
          (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
          P O C3 link hlink))).toStepXIFiniteCertificate) :
    (∀ b : Bad (nativePlaceSelection T),
      s994VR T In b ≤ s994VS T In b) ∧
      weightedPaperV T (s994VR T In) ≤
        weightedPaperV T (s994VS T In) ∧
      Cor312Conclusion
        ((paperCertificate (I := paperXiFInput
          (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
            (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
            P O C3 link hlink))).toContract
          (paperSignedLinkEvidence
            (I := paperXiFInput
              (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
                (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
                P O C3 link hlink)) links)) := by
  refine ⟨?_, s994GlobalWeightedInequality T In, ?_⟩
  · intro b
    exact (s994PerBLogComparison T b
      { linearization := In.L b
        qPilot_pos := In.qPilot_pos b
        hull_finite := In.hull_finite b }).2
  · exact paperAssembly_cor312Conclusion
      (link := link) (link_holds := hlink) (links := links)
/-- Projection theorem: the target is exactly `Cor312Conclusion`, not the
three-way conjunction.  Proof is the `.2.2` projection of
`s995FiniteCarrierCor312Conclusion`; mathematical content unchanged. -/
theorem s995Cor312Conclusion
    (In : S994FiniteInput T)
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
  (s995FiniteCarrierCor312Conclusion (T := T) (P := P) (O := O) (C3 := C3)
    In link hlink links).2.2
end LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual
