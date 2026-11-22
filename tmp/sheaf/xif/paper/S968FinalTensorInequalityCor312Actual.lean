import tmp.sheaf.xif.paper.S962TensorPacketPaperInequalityActual
import tmp.sheaf.xif.paper.S858PaperGapConditionalCor312Actual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual

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
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S957TensorClosureContainmentActual
open LeanFormal.IUT.XiFPaper.S962TensorPacketPaperInequalityActual
open LeanFormal.IUT.XiFPaper.S858PaperGapConditionalCor312Actual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uW uX uLabel uK
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (O : PaperQPilotObject (l := l) (V := V)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
variable (C3 : SourcePilotRegionData I)
variable {l0 : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l0)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (D : ∀ b : Bad (nativePlaceSelection T),
  FinalLTensorLogVolumeData T b)

/-- Inclusion constructor from an explicit PaperXiFSourceLink and its link. -/
noncomputable def s968Inclusion
    (link : PaperXiFSourceLink O P C3)
    (hlink : link.link_identification) :
    PaperXiFInclusion O P C3 where
  link := link
  link_holds := hlink

/-- Final conditional assembly: tensor density/positivity/finiteness/log-volume
data plus an explicit source link and finite links imply the tensor weighted
inequality and Cor312Conclusion.  No equality/scaling data. -/
theorem paperCor312_of_tensorInequality
    [Nonempty label]
    (hdensity : ∀ b : Bad (nativePlaceSelection T),
      S957ThetaImageDenseInQPilot T b (D b))
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < (D b).measure (qPilotPaperImageInLValued T b))
    (hfin : ∀ b : Bad (nativePlaceSelection T),
      (D b).measure (paperTensorHull T b (D b)) < ⊤)
    (link : PaperXiFSourceLink O P C3)
    (hlink : link.link_identification)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (s968Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
          (G' := G') (envStrip := envStrip) P O C3 link hlink))).toStepXIFiniteCertificate) :
    tensorPacketPaperWeightedInequality (l := l0) T D ∧
      Cor312Conclusion
        ((paperCertificate (I := paperXiFInput
          (s968Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
            (G' := G') (envStrip := envStrip) P O C3 link hlink))).toContract
          (paperSignedLinkEvidence
            (I := paperXiFInput
              (s968Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
                (G' := G') (envStrip := envStrip) P O C3 link hlink)) links)) := by
  constructor
  · exact tensorPacketPaperWeightedInequality_of_perB (l := l0) T D
      hdensity hpos hfin
  · exact paperAssembly_cor312Conclusion
      (link := link) (link_holds := hlink) (links := links)

/-- Exact hypothesis package for the tensor part. -/
def S968TensorHypotheses
    (D : ∀ b : Bad (nativePlaceSelection T), FinalLTensorLogVolumeData T b) : Prop :=
  (∀ b : Bad (nativePlaceSelection T),
    S957ThetaImageDenseInQPilot T b (D b)) ∧
  (∀ b : Bad (nativePlaceSelection T),
    0 < (D b).measure (qPilotPaperImageInLValued T b)) ∧
  (∀ b : Bad (nativePlaceSelection T),
    (D b).measure (paperTensorHull T b (D b)) < ⊤)

end LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual

end
