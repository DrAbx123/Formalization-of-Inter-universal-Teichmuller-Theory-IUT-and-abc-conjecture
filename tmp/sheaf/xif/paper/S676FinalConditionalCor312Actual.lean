import tmp.sheaf.xif.paper.S669S663PaperXiFSourceLinkActual
import tmp.sheaf.xif.PaperAssembly

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S676FinalConditionalCor312Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S663ActualAverageNormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S669S663PaperXiFSourceLinkActual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uW uX uLabel uK
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip V}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota → Type uW}
variable (places : (i : iota) → W i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (O : PaperQPilotObject (l := l) (V := V)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
variable (C3 : SourcePilotRegionData I)

/-- The S669 source link with actual S663 theta hull. -/
noncomputable def s676SourceLink
    [Nonempty (SignedLabel l.value)]
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : S669QPilotLogVolumeEqPaper O C3)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈
        hullLogVolumeRay (s663PaperSignedHull (l := l) (K := K) (p := p)
          places tuple nu T b).signedHullLogVolume) :
    PaperXiFSourceLink O
      (s663PaperSignedHull (l := l) (K := K) (p := p) places tuple nu T b) C3 :=
  s669PaperXiFSourceLink (l := l) (I := I) (V := V)
    (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
    (K := K) (p := p) (places := places) (tuple := tuple) (nu := nu)
    T b O C3 hident hqpaper link_identification link_implies_inclusion

/-- Conditional final chain from the S669 paper xi-f inclusion to the paper
certificate and Cor312Conclusion, with explicit finite link evidence. -/
theorem s676_finalCor312
    [Nonempty (SignedLabel l.value)]
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : S669QPilotLogVolumeEqPaper O C3)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈
        hullLogVolumeRay (s663PaperSignedHull (l := l) (K := K) (p := p)
          places tuple nu T b).signedHullLogVolume)
    (hlink : link_identification)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (⟨s676SourceLink (l := l) (I := I) (V := V)
          (places := places) (tuple := tuple) (nu := nu) T b O C3
          hident hqpaper link_identification link_implies_inclusion,
          hlink⟩ : PaperXiFInclusion O
            (s663PaperSignedHull (l := l) (K := K) (p := p)
              places tuple nu T b) C3))).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((paperCertificate (I := paperXiFInput
        (⟨s676SourceLink (l := l) (I := I) (V := V)
          (places := places) (tuple := tuple) (nu := nu) T b O C3
          hident hqpaper link_identification link_implies_inclusion,
          hlink⟩ : PaperXiFInclusion O
            (s663PaperSignedHull (l := l) (K := K) (p := p)
              places tuple nu T b) C3))).toContract
        (paperSignedLinkEvidence (I := paperXiFInput
          (⟨s676SourceLink (l := l) (I := I) (V := V)
            (places := places) (tuple := tuple) (nu := nu) T b O C3
            hident hqpaper link_identification link_implies_inclusion,
            hlink⟩ : PaperXiFInclusion O
              (s663PaperSignedHull (l := l) (K := K) (p := p)
                places tuple nu T b) C3)) links)) := by
  exact paperAssembly_cor312Conclusion
    (link := s676SourceLink (l := l) (I := I) (V := V)
      (places := places) (tuple := tuple) (nu := nu) T b O C3
      hident hqpaper link_identification link_implies_inclusion)
    (link_holds := hlink) (links := links)

end LeanFormal.IUT.XiFPaper.S676FinalConditionalCor312Actual

end
