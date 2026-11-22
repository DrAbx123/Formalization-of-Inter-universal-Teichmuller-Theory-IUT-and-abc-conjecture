import tmp.sheaf.xif.paper.S995FiniteCarrierCor312ConclusionActual
import tmp.sheaf.xif.paper.S1025S994FiniteInputActual

/-! # S1029: final S995 audit after S1025 actual S994FiniteInput

S1025 supplies an actual S994FiniteInput.  This file uses it in S995 and prints
the target/axioms of the resulting Cor312Conclusion.  Remaining exact inputs are
only the PaperXiFSourceLink fields (hQ/hC3 via S991), hlink and finite links.
No S994FiniteInput positivity/finiteness remains. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1029S995FinalAuditActual

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
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uX uLabel u uC3 uD3 uM uP

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

/-- S995 with the actual S1025 finite input.  Only the source link and finite
link evidence remain as explicit inputs. -/
theorem s1029S995Cor312Conclusion
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
  s995Cor312Conclusion (T := T) (P := P) (O := O) (C3 := C3)
    (s994FiniteInput_actual (l := l) T) link hlink links

#print axioms s994FiniteInput_actual
#print axioms nonempty_s994FiniteInput
#print axioms s995Cor312Conclusion
#print axioms s1029S995Cor312Conclusion

end LeanFormal.IUT.XiFPaper.S1029S995FinalAuditActual

end
