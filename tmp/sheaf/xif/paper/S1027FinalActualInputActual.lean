import tmp.sheaf.xif.paper.S995FiniteCarrierCor312ConclusionActual
import tmp.sheaf.xif.paper.S1025S994FiniteInputActual

/-! # S1027: final S995 with the actual S994FiniteInput

S1025 supplies an actual S994FiniteInput, so the positivity/finiteness exact
fields are gone.  What remains are the source link, its identification, and
the finite link evidence; S1009/S1017 identify the source-q part of the link. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1027FinalActualInputActual

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
open LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual
open LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual
open LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
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

/-- Final finite-carrier Cor312Conclusion using the actual S994FiniteInput.
Only link/hlink/finite links remain as inputs. -/
theorem s1027FiniteCarrierCor312Conclusion
    (link : PaperXiFSourceLink O P C3)
    (hlink : link.link_identification)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
          (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
          P O C3 link hlink))).toStepXIFiniteCertificate) :
    (∀ b : Bad (nativePlaceSelection T),
      s994VR T (s994FiniteInput_actual (l := l) T) b ≤
        s994VS T (s994FiniteInput_actual (l := l) T) b) ∧
      weightedPaperV T (s994VR T (s994FiniteInput_actual (l := l) T)) ≤
        weightedPaperV T (s994VS T (s994FiniteInput_actual (l := l) T)) ∧
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
  s995FiniteCarrierCor312Conclusion (T := T) (P := P) (O := O) (C3 := C3)
    (s994FiniteInput_actual (l := l) T) link hlink links

include T

/-- Exact remaining list: link, hlink, finite link evidence; sourceQ is the
hQ component of the supplied link. -/
def S1027ExactRemaining
    (link : PaperXiFSourceLink O P C3) : Prop :=
  link.link_identification

end LeanFormal.IUT.XiFPaper.S1027FinalActualInputActual
end