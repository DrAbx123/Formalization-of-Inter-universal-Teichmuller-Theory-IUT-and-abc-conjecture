import tmp.sheaf.xif.paper.PaperC3SourceDataQConsistencyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalAbsorption

/-! # Actual one-factor tensor landing/unit for source q data

The one-factor tensor block is a pure tensor of the completion.  The tensor
landing is `x |-> tprod (fun _ => x)`, and the tensor unit is the pure tensor of
the qVFamily q, whose inverse exists because q != 0.  This closes the
tensorUnit/tensorLanding compatibility without `tensorUnit = 1`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3SourceDataQTensorActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.LocalFieldPadicTensor

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def sourceQTensorLanding
    (x : CommonPrimeCompletion (sourceThetaPlace T b)) :
    SourceQTensorBlock T b :=
  arithmeticTupleTprod
    (fun _ (_ : Unit) => sourceThetaPlace T b) (fun _ => ())
    (fun _ : PUnit => x)

theorem sourceQTensorLanding_apply
    (x : CommonPrimeCompletion (sourceThetaPlace T b)) :
    sourceQTensorLanding (T := T) b x =
      arithmeticTupleTprod
        (fun _ (_ : Unit) => sourceThetaPlace T b) (fun _ => ())
        (fun _ : PUnit => x) := rfl

noncomputable def sourceQTensorUnit : (SourceQTensorBlock T b)ˣ :=
  Units.mkOfMulEqOne
    (sourceQTensorLanding (T := T) b (qVFamily T b).q)
    (sourceQTensorLanding (T := T) b ((qVFamily T b).q)⁻¹)
    (by
      rw [sourceQTensorLanding_apply, sourceQTensorLanding_apply,
        ← arithmeticTupleTprod_mul]
      have hq : (qVFamily T b).q ≠ 0 := (qVFamily T b).q_ne_zero
      simp [mul_inv_cancel₀ hq])

theorem sourceQTensorUnit_val :
    (sourceQTensorUnit (T := T) b : SourceQTensorBlock T b) =
      sourceQTensorLanding (T := T) b (qVFamily T b).q := rfl

theorem sourceQTensorLanding_q :
    sourceQTensorLanding (T := T) b (qVFamily T b).q =
      (sourceQTensorUnit (T := T) b : SourceQTensorBlock T b) := rfl

noncomputable def sourcePilotRegionQDataActual :
    SourcePilotRegionQData T b where
  tensorUnit := sourceQTensorUnit (T := T) b
  tensorLanding := sourceQTensorLanding (T := T) b
  tensorLanding_q := sourceQTensorLanding_q (T := T) b

end LeanFormal.IUT.XiFPaper.PaperC3SourceDataQTensorActualAdapted

end
