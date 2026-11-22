import tmp.sheaf.xif.paper.S663ActualAverageNormalizedHaarActual
import tmp.sheaf.xif.PaperXiFInclusion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S669S663PaperXiFSourceLinkActual

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
open LeanFormal.IUT.XiFPaper.S658RootNormalizedPaperSignedHullActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
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

/-- Explicit q-pilot/paper log equality field. -/
def S669QPilotLogVolumeEqPaper
    (O : PaperQPilotObject (l := l) (V := V)
      (Label := Label) (Choice := Choice) (I := I) G' envStrip)
    (C3 : SourcePilotRegionData I) : Prop :=
  O.qPilotLogVolume = paperQPilotLogVolume C3

/-- Conditional PaperXiFSourceLink with S663 actual theta hull; only source
identifications, qPilot/paper log equality, and the link fields are explicit. -/
noncomputable def s669PaperXiFSourceLink
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
      (s663PaperSignedHull (l := l) (K := K) (p := p) places tuple nu T b) C3 where
  source_identifications := hident
  qPilotLogVolume_eq_paper := hqpaper
  link_identification := link_identification
  link_implies_inclusion := link_implies_inclusion

/-- PaperXiFInclusion once the explicit link identification is supplied. -/
noncomputable def s669PaperXiFInclusion
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : S669QPilotLogVolumeEqPaper (l := l) (V := V) (I := I)
      (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip) O C3)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈
        hullLogVolumeRay (s663PaperSignedHull (l := l) (K := K) (p := p)
          places tuple nu T b).signedHullLogVolume)
    (hlink : link_identification) :
    PaperXiFInclusion O
      (s663PaperSignedHull (l := l) (K := K) (p := p) places tuple nu T b) C3 where
  link := s669PaperXiFSourceLink (l := l) (V := V) (I := I)
    (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
    (K := K) (p := p) (places := places) (tuple := tuple) (nu := nu)
    T b O C3 hident hqpaper link_identification link_implies_inclusion
  link_holds := hlink

/-- The resulting paper xi-f membership in the signed hull ray. -/
theorem s669_qPilot_mem_ray
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : S669QPilotLogVolumeEqPaper (l := l) (V := V) (I := I)
      (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip) O C3)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈
        hullLogVolumeRay (s663PaperSignedHull (l := l) (K := K) (p := p)
          places tuple nu T b).signedHullLogVolume)
    (hlink : link_identification) :
    O.qPilotLogVolume ∈
      hullLogVolumeRay (s663PaperSignedHull (l := l) (K := K) (p := p)
        places tuple nu T b).signedHullLogVolume :=
  (s669PaperXiFInclusion (l := l) (V := V) (I := I)
    (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
    (K := K) (p := p) (places := places) (tuple := tuple) (nu := nu)
    T b O C3 hident hqpaper link_identification link_implies_inclusion hlink).qPilot_mem_ray

end LeanFormal.IUT.XiFPaper.S669S663PaperXiFSourceLinkActual

end
