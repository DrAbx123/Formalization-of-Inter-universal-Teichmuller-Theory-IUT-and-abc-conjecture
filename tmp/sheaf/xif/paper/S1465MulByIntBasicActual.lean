import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
/-! # S1465: minimal port of TauCeti Isogeny/MulByInt basic layer
Ports only the coordinate-pullback/Isogeny definitions and the psi/phi/omega
function-field elements.  The mulByIntPullback, mulByIntIsogeny, fieldPullback
and ker construction need the generic point API
(WeierstrassCurve.Affine.genericX/genericY, equation_genericX_genericY), which is
NOT in Mathlib v4.32.2; exact first field is recorded in the final section.
Dependency table:
  TauCeti Affine/Eval.lean                    -> Mathlib Point/DivisionPolynomial
  TauCeti Affine/FunctionField/GenericPoint   -> MISSING (first dep)
  TauCeti DivisionPolynomial/ZSMul           -> MISSING (zsmul_eq_smulEval)
  TauCeti Isogeny/Basic                       -> ported here
  TauCeti MulByInt/Basic (psiFunctionField)   -> partially ported here
  TauCeti MulByInt/MapsInfinity, Kernel       -> blocked on genericPoint/ZSMul
No vendor of the full closure. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1465MulByIntBasicActual
open Polynomial
open scoped Polynomial.Bivariate
namespace TauCeti
open _root_.WeierstrassCurve.Affine
variable {F : Type*} [Field F]
abbrev CoordinatePullback (W₁ W₂ : WeierstrassCurve.Affine F) : Type _ :=
  W₂.CoordinateRing →ₐ[F] W₁.FunctionField
namespace CoordinatePullback
def MapsInfinity {W₁ W₂ : WeierstrassCurve.Affine F}
    (pullback : CoordinatePullback W₁ W₂) : Prop :=
  letI := pullback.toRingHom.toAlgebra
  ∀ x : W₁.CoordinateRing,
    algebraMap W₁.CoordinateRing W₁.FunctionField x ∈
      integralClosure W₂.CoordinateRing W₁.FunctionField
theorem mapsInfinity_iff {W₁ W₂ : WeierstrassCurve.Affine F}
    (pullback : CoordinatePullback W₁ W₂) :
    pullback.MapsInfinity ↔ ∀ x : W₁.CoordinateRing,
      @IsIntegral W₂.CoordinateRing W₁.FunctionField _ _ pullback.toRingHom.toAlgebra
        (algebraMap W₁.CoordinateRing W₁.FunctionField x) := Iff.rfl
theorem mapsInfinity_of_pow {W₁ W₂ : WeierstrassCurve.Affine F}
    (pullback : CoordinatePullback W₁ W₂) {n : ℕ} (hn : 0 < n)
    (h : ∀ z : W₁.CoordinateRing, ∃ w : W₂.CoordinateRing,
      pullback w = algebraMap W₁.CoordinateRing W₁.FunctionField z ^ n) :
    pullback.MapsInfinity := by
  rw [mapsInfinity_iff]
  let _ := pullback.toRingHom.toAlgebra
  intro z
  obtain ⟨w, hw⟩ := h z
  refine IsIntegral.of_pow hn ?_
  rw [← hw]
  rw [← AlgHom.coe_toRingHom, ← RingHom.algebraMap_toAlgebra pullback.toRingHom]
  exact isIntegral_algebraMap
noncomputable def id (W : WeierstrassCurve.Affine F) : CoordinatePullback W W :=
  IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField
@[simp] theorem id_apply (W : WeierstrassCurve.Affine F) (x : W.CoordinateRing) :
    id W x = algebraMap W.CoordinateRing W.FunctionField x := by
  unfold id
  exact IsScalarTower.toAlgHom_apply F W.CoordinateRing W.FunctionField x
theorem mapsInfinity_id (W : WeierstrassCurve.Affine F) :
    ∀ x : W.CoordinateRing,
      @IsIntegral W.CoordinateRing W.FunctionField _ _ (id W).toRingHom.toAlgebra
        (algebraMap W.CoordinateRing W.FunctionField x) := by
  have h : (id W).toRingHom.toAlgebra =
      (inferInstance : Algebra W.CoordinateRing W.FunctionField) := by
    apply Algebra.algebra_ext
    intro x
    rw [RingHom.algebraMap_toAlgebra]
    exact id_apply W x
  rw [h]
  exact fun _ => isIntegral_algebraMap
end CoordinatePullback
structure Isogeny (W₁ W₂ : WeierstrassCurve.Affine F) where
  pullback : CoordinatePullback W₁ W₂
  mapsInfinity : pullback.MapsInfinity
namespace Isogeny
noncomputable def id (W : WeierstrassCurve.Affine F) : Isogeny W W where
  pullback := CoordinatePullback.id W
  mapsInfinity := (CoordinatePullback.mapsInfinity_iff _).2
    (CoordinatePullback.mapsInfinity_id W)
@[simp] theorem id_pullback (W : WeierstrassCurve.Affine F) :
    (id W).pullback = CoordinatePullback.id W := rfl
noncomputable def psiFunctionField (W : WeierstrassCurve.Affine F) (n : ℤ) :
    W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.ψ n))
noncomputable def phiFunctionField (W : WeierstrassCurve.Affine F) (n : ℤ) :
    W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.φ n))
noncomputable def mulByIntX (W : WeierstrassCurve.Affine F) (n : ℤ) :
    W.FunctionField :=
  phiFunctionField W n / psiFunctionField W n ^ 2
theorem psiFunctionField_def (W : WeierstrassCurve.Affine F) (n : ℤ) :
    psiFunctionField W n =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (W.ψ n)) := rfl
theorem mulByIntX_def (W : WeierstrassCurve.Affine F) (n : ℤ) :
    mulByIntX W n = phiFunctionField W n / psiFunctionField W n ^ 2 := rfl
end Isogeny
end TauCeti
end LeanFormal.IUT.XiFPaper.S1465MulByIntBasicActual
