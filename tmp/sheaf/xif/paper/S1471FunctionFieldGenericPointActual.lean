import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
/-! # S1471: generic point coordinates over Mathlib v4.32.2
Actual definitions of genericX/genericY via the affine coordinate ring and
function field.  The equation/API theorem requires the TauCeti coordinate-ring
evaluation identity `evalEval_genericX_genericY` (equivalently
CoordinateRing.algHom_mk_eq_evalEval and mk_C_eq_algebraMap), which are absent
from Mathlib v4.32.2.  Exact first field recorded in the final comment. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace WeierstrassCurve.Affine
open Polynomial
open scoped Polynomial.Bivariate
variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve.Affine R)
/-- The generic x-coordinate: class of X in the function field. -/
noncomputable def genericX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))
/-- The generic y-coordinate: class of Y in the function field. -/
noncomputable def genericY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
@[simp] theorem genericX_def :
    genericX W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X)) := rfl
@[simp] theorem genericY_def :
    genericY W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) := rfl
-- Exact first missing TauCeti lemma:
-- evalEval_genericX_genericY :
--   (p.map (mapRingHom (algebraMap R W.FunctionField))).evalEval genericX genericY =
--     algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p)
-- This needs CoordinateRing.algHom_mk_eq_evalEval (not in Mathlib v4.32.2).
-- Consequently equation_genericX_genericY and genericPoint are not constructed.
end WeierstrassCurve.Affine
end
