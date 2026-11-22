import tmp.sheaf.xif.paper.S979TensorRegionHullInequalityActual
import tmp.sheaf.xif.paper.S990FiniteCarrierPositivityFinitenessActual
import tmp.sheaf.xif.paper.S980QPilotImagePositivityActual
import tmp.sheaf.xif.paper.S991S983LinkInputsActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S992FinalIntegrationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual
open LeanFormal.IUT.XiFPaper.S990FiniteCarrierPositivityFinitenessActual
open LeanFormal.IUT.XiFPaper.S980QPilotImagePositivityActual
open LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual
open LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual
open LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uW uX uLabel uK u uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)
variable (b : Bad (nativePlaceSelection T))

/-- S990/S980 fill S979 positivity and finiteness. -/
theorem s992S979Hypotheses
    (D : ∀ b : Bad (nativePlaceSelection T),
      FinalLTensorLogVolumeData (l := l) T b)
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      S980FinalLImageInteriorExactInput (l := l) T b (D b))
    (hfin : ∀ b : Bad (nativePlaceSelection T),
      S990HullFinitenessInput (l := l) T b (D b)) :
    S979TensorRegionHypotheses (l := l) T D := by
  constructor
  · intro b
    exact s980FinalLImage_measure_pos (l := l) T b (D b) (hpos b)
  · intro b
    exact s990TensorRegionHull_measure_lt_top (l := l) T b (D b) (hfin b)

/-- S991/S983 actual concrete source link. -/
noncomputable def s992ConcreteLink
    (Oa : PaperQPilotObjectActual.{0, 0, 0, 0, 0, uC3, uD3, uM, uP}
      (l := l) (V := FinitePrimePlace 2 7) (I := I))
    (hC3 : Oa.line.C3 = C3)
    (hQ : (concreteO (l := l) I).qPilotLogVolume = paperQPilotLogVolume C3) :
    PaperXiFSourceLink (concreteO (l := l) I) P C3 :=
  s991PaperXiFSourceLink (l := l) I P C3 Oa hC3 hQ

/-- Final conditional Cor312 assembly: S990/S980 tensor positivity/finiteness,
S991/S983 concrete link available separately, and an explicit source link.
Inequality only. -/
theorem paperCor312_of_finiteCarrierExact
    [Nonempty label]
    (Oa : PaperQPilotObjectActual.{0, 0, 0, 0, 0, uC3, uD3, uM, uP}
      (l := l) (V := FinitePrimePlace 2 7) (I := I))
    (hC3 : Oa.line.C3 = C3)
    (hQ : (concreteO (l := l) I).qPilotLogVolume = paperQPilotLogVolume C3)
    (D : ∀ b : Bad (nativePlaceSelection T),
      FinalLTensorLogVolumeData (l := l) T b)
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      S980FinalLImageInteriorExactInput (l := l) T b (D b))
    (hfin : ∀ b : Bad (nativePlaceSelection T),
      S990HullFinitenessInput (l := l) T b (D b))
    (link : PaperXiFSourceLink O P C3)
    (hlink : link.link_identification)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (S968FinalTensorInequalityCor312Actual.s968Inclusion
          (l := l) (V := FinitePrimePlace 2 7) (Label := Label) (Choice := Choice)
          (G' := G') (envStrip := envStrip) P O C3 link hlink))).toStepXIFiniteCertificate) :
    tensorRegionHullPaperWeightedInequality (l := l) T D ∧
      Cor312Conclusion
        ((paperCertificate (I := paperXiFInput
          (S968FinalTensorInequalityCor312Actual.s968Inclusion
            (l := l) (V := FinitePrimePlace 2 7) (Label := Label) (Choice := Choice)
            (G' := G') (envStrip := envStrip) P O C3 link hlink))).toContract
          (paperSignedLinkEvidence
            (I := paperXiFInput
              (S968FinalTensorInequalityCor312Actual.s968Inclusion
                (l := l) (V := FinitePrimePlace 2 7) (Label := Label) (Choice := Choice)
                (G' := G') (envStrip := envStrip) P O C3 link hlink)) links)) := by
  exact paperCor312_of_tensorRegionInequality (l := l) T
    (D := D) P O C3 (s992S979Hypotheses (l := l) T (D := D) hpos hfin) link hlink links

/-- Concrete link from S991 is an actual source link; recorded separately. -/
theorem s992ConcreteLink_actual
    (Oa : PaperQPilotObjectActual.{0, 0, 0, 0, 0, uC3, uD3, uM, uP}
      (l := l) (V := FinitePrimePlace 2 7) (I := I))
    (hC3 : Oa.line.C3 = C3)
    (hQ : (concreteO (l := l) I).qPilotLogVolume = paperQPilotLogVolume C3) :
    Nonempty (PaperXiFSourceLink (concreteO (l := l) I) P C3) :=
  ⟨s992ConcreteLink (l := l) P C3 Oa hC3 hQ⟩

end LeanFormal.IUT.XiFPaper.S992FinalIntegrationActual

end
