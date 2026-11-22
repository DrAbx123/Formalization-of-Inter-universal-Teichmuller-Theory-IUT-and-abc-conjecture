import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-! # S214: rootThetaNorm and the L tensor theta norm/hull transport

The one-factor tensor block is linearly equivalent to L.  The actual tensor theta
image maps to rootNormedThetaValueInL, so its transported L norm is the actual L
norm; the tensor theta hull is the linear-equivalence preimage of the L closure
hull.  No topology on the tensor block is assumed.

No inequality/no fake norm/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S214RootThetaNormTensorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Concrete linear equivalence rootTensorBlock ≃ L. -/
noncomputable def tensorBlockLinearEquiv :
    rootTensorBlock T b ≃ₗ[ℚ_[(qVFamTensorP T b)]] rootNormedExtension T b :=
  PiTensorProduct.subsingletonEquiv (R := ℚ_[(qVFamTensorP T b)])
    (s := fun _ : Unit => rootNormedExtension T b) (ι := Unit) (i₀ := ())

/-- The tensor theta image maps to the L theta value. -/
theorem tensorBlockLinearEquiv_thetaImage (j : SignedLabel l.value) :
    tensorBlockLinearEquiv T b (rootTensorThetaImage T b j) =
      rootNormedThetaValueInL T b j := by
  unfold tensorBlockLinearEquiv rootTensorThetaImage
  change (PiTensorProduct.subsingletonEquiv (R := ℚ_[(qVFamTensorP T b)])
      (s := fun _ : Unit => rootNormedExtension T b) (ι := Unit) (i₀ := ()))
      (PiTensorProduct.tprod ℚ_[(qVFamTensorP T b)]
        (fun _ : Unit => (rootNormedThetaValueInL T b j : rootNormedExtension T b))) =
    rootNormedThetaValueInL T b j
  exact PiTensorProduct.subsingletonEquiv_apply_tprod
    (R := ℚ_[(qVFamTensorP T b)])
    (s := fun _ : Unit => rootNormedExtension T b) (i₀ := ()) _

/-- Transported tensor theta norm: tensor theta image mapped into L and measured
by the actual L norm. -/
noncomputable def transportedTensorThetaNorm (j : SignedLabel l.value) : Real :=
  ‖tensorBlockLinearEquiv T b (rootTensorThetaImage T b j)‖

theorem transportedTensorThetaNorm_eq
    (j : SignedLabel l.value) :
    transportedTensorThetaNorm T b j =
      ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ := by
  unfold transportedTensorThetaNorm
  rw [tensorBlockLinearEquiv_thetaImage]

theorem transportedTensorThetaNorm_eq_rootNormedElementNorm
    (j : SignedLabel l.value) :
    transportedTensorThetaNorm T b j =
      (rootNormedElementNorm T b) ^ (gaussExponent j.1) := by
  rw [transportedTensorThetaNorm_eq, rootNormedThetaValueInL_norm]
  rfl

/-- L theta closure hull. -/
noncomputable def LThetaClosureHull : Set (rootNormedExtension T b) :=
  closure (Set.range (rootNormedThetaValueInL T b))

/-- Tensor theta hull as the linear-equivalence preimage of the L closure hull. -/
noncomputable def tensorThetaHullPreimage : Set (rootTensorBlock T b) :=
  (tensorBlockLinearEquiv T b) ⁻¹' (LThetaClosureHull T b)

/-- The tensor theta image set maps exactly to the L theta value range. -/
theorem tensorBlockLinearEquiv_image_thetaImageSet :
    tensorBlockLinearEquiv T b '' Set.range (rootTensorThetaImage T b) =
      Set.range (rootNormedThetaValueInL T b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨j, rfl⟩
    exact ⟨j, (tensorBlockLinearEquiv_thetaImage T b j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨rootTensorThetaImage T b j, ⟨j, rfl⟩,
      tensorBlockLinearEquiv_thetaImage T b j⟩

/-- Actual compatibility object between O-triangle root normalization and the
L/tensor theta hull. -/
structure RootThetaNormTensorHullCompatibility where
  rootNormObject : RootThetaNormLObject (l := l) T b
  tensorThetaImage : SignedLabel l.value → rootTensorBlock T b
  tensorThetaImage_eq : tensorThetaImage = rootTensorThetaImage T b
  tensorThetaNorm : SignedLabel l.value → Real
  tensorThetaNorm_eq : tensorThetaNorm = transportedTensorThetaNorm T b
  tensorThetaNorm_eq_L : ∀ j,
    tensorThetaNorm j = ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖
  tensorHull : Set (rootTensorBlock T b)
  tensorHull_eq : tensorHull = tensorThetaHullPreimage T b
  LThetaHull : Set (rootNormedExtension T b)
  LThetaHull_eq : LThetaHull = LThetaClosureHull T b
  hull_compat : tensorBlockLinearEquiv T b '' tensorHull = LThetaHull

/-- Actual root theta norm/tensor hull compatibility object. -/
noncomputable def rootThetaNormTensorHullCompatibility :
    RootThetaNormTensorHullCompatibility (l := l) T b where
  rootNormObject := rootThetaNormLObject T b
  tensorThetaImage := rootTensorThetaImage T b
  tensorThetaImage_eq := rfl
  tensorThetaNorm := transportedTensorThetaNorm T b
  tensorThetaNorm_eq := rfl
  tensorThetaNorm_eq_L := fun j => transportedTensorThetaNorm_eq T b j
  tensorHull := tensorThetaHullPreimage T b
  tensorHull_eq := rfl
  LThetaHull := LThetaClosureHull T b
  LThetaHull_eq := rfl
  hull_compat := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨(tensorBlockLinearEquiv T b).symm y, ?_, ?_⟩
      · change tensorBlockLinearEquiv T b
          ((tensorBlockLinearEquiv T b).symm y) ∈ LThetaClosureHull T b
        rw [LinearEquiv.apply_symm_apply]
        exact hy
      · exact (tensorBlockLinearEquiv T b).apply_symm_apply y

end LeanFormal.IUT.XiFPaper.S214RootThetaNormTensorActual

end
