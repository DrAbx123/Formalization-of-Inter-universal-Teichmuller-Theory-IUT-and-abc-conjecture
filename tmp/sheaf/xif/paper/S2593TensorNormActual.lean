import tmp.sheaf.xif.paper.S2591PointLocalLogDegreeActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2593TensorNormActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

local instance S2593Algebra : Algebra T.arithmetic.F
    (CommonPrimeCompletion (qVFamTensorPlaces T b () ())) :=
  inferInstanceAs (Algebra T.arithmetic.F
    (LeanFormal.IUT.NumberFieldFinitePlace.Completion
      (qVFamTensorPlaces T b () ()).val))

theorem S2593TensorNorm
    (z : CommonPrimeCompletion (qVFamTensorPlaces T b () ())) :
    ‖(finitePadicTensorTprod (p := qVFamTensorP T b)
        (fun _ : Unit => CommonPrimeCompletion (qVFamTensorPlaces T b () ())))
        (fun _ => z)‖ =
      ‖fun j : Unit → Fin (Module.finrank ℚ_[qVFamTensorP T b]
          (CommonPrimeCompletion (qVFamTensorPlaces T b () ()))) =>
        (Module.finBasis ℚ_[qVFamTensorP T b]
          (CommonPrimeCompletion (qVFamTensorPlaces T b () ()))).repr z (j ())‖ := by
  rw [show (finitePadicTensorTprod (p := qVFamTensorP T b)
      (fun _ : Unit => CommonPrimeCompletion (qVFamTensorPlaces T b () ())))
      (fun _ => z) = finitePadicTensorTprod (p := qVFamTensorP T b)
      (fun _ : Unit => CommonPrimeCompletion (qVFamTensorPlaces T b () ()))
      (fun _ => z) from rfl]
  -- the tensor norm is induced by coordinates
  change ‖(finitePadicTensorCoordinates (p := qVFamTensorP T b)
      (fun _ : Unit => CommonPrimeCompletion (qVFamTensorPlaces T b () ())))
      ((finitePadicTensorTprod (p := qVFamTensorP T b)
        (fun _ : Unit => CommonPrimeCompletion (qVFamTensorPlaces T b () ())))
        (fun _ => z))‖ = _
  congr 1
  funext j
  rw [finitePadicTensorCoordinates_tprod]
  simp

#check S2593TensorNorm

theorem S2593PointMapNorm
    (a n c : Nat) :
    ‖S2588PointMap T b a n c‖ =
      ‖fun j : Unit → Fin (Module.finrank ℚ_[qVFamTensorP T b]
          (CommonPrimeCompletion (qVFamTensorPlaces T b () ()))) =>
        (Module.finBasis ℚ_[qVFamTensorP T b]
          (CommonPrimeCompletion (qVFamTensorPlaces T b () ()))).repr
          (algebraMap T.arithmetic.F
            (CommonPrimeCompletion (qVFamTensorPlaces T b () ()))
            (algebraMap Rat T.arithmetic.F (abcRationalPoint a c))) (j ())‖ := by
  rw [S2588PointMap]
  exact S2593TensorNorm T b _

#check S2593PointMapNorm
end LeanFormal.IUT.XiFPaper.S2593TensorNormActual
end