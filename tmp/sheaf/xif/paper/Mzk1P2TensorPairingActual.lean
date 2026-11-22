import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import Mathlib.Tactic

/-! # P2: tensor determinant pairing and product-formula cancellation

The pairing is the actual tensor determinant norm of the coefficient family.
The cancellation lemma is algebraic: once the finite part is known to be the
negative of the weighted determinant log, the archimedean part equals it.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2TensorPairingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2DetCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Tensor determinant pairing value of a pure coefficient family. -/
noncomputable def tensorDetPairing (c : RootExtensionProductCarrier T) : Real :=
  detCoefficientNorm T c

theorem tensorDetPairing_eq_prod (c : RootExtensionProductCarrier T) :
    tensorDetPairing T c =
      ∏ b : Bad (nativePlaceSelection T), ‖c b‖ := rfl

/-- Algebraic product-formula cancellation: arch + finite = 0 and
finite = -weighted gives arch = weighted. -/
theorem productFormula_cancel {arch finite weighted : Real}
    (hfull : arch + finite = 0) (hfinite : finite = -weighted) :
    arch = weighted := by
  linarith

/-- Tensor pairing cancellation form. -/
theorem tensorPairing_cancel_of_finite {arch finite : Real}
    (c : RootExtensionProductCarrier T)
    (hfull : arch + finite = 0)
    (hfinite : finite = -Real.log (tensorDetPairing T c)) :
    arch = Real.log (tensorDetPairing T c) :=
  productFormula_cancel hfull hfinite

/-- The finite part is the negative weighted determinant log of the actual
pure tensor coefficients. -/
theorem p2TensorPairing_finite_eq (finite : Real)
    (hfinite : finite = -p2WeightedDetLog T) :
    finite = -∑ b : Bad (nativePlaceSelection T),
      (s1915LocalDegree T b : Real) * Real.log ‖p2Coefficient T b‖ := by
  rw [hfinite]
  rfl

#check tensorDetPairing
#check tensorDetPairing_eq_prod
#check productFormula_cancel
#check tensorPairing_cancel_of_finite
#check p2TensorPairing_finite_eq
end LeanFormal.IUT.XiFPaper.Mzk1P2TensorPairingActual
end
