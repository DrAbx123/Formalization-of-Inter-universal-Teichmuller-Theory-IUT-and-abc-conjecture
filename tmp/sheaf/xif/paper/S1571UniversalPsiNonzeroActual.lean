import tmp.sheaf.xif.paper.S1569AffineRecursionNonzeroActual
import tmp.sheaf.xif.paper.S1535UniversalRecursionActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual
/-! # S1571: universal psi nonvanishing
Exact target: polyToField (curve.toAffine.psi n) != 0 for n != 0.
The TauCeti proof (Universal.lean polyToField_psi_ne_zero) specializes the
universal curve at the cusp (1,1), where psi_n evaluates to n.  Mathlib
v4.32.2 has no cusp curve, no Universal.polyEval/ringEval, and no
polyEval_cusp_psi, so this file records the exact first missing chain instead
of assuming nonvanishing. -/
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Universal
variable (n : ℤ)
/-- Exact target, not asserted: universal psi nonvanishing in Universal.Field. -/
abbrev S1571UniversalPsiNonzero : Prop :=
  ∀ n : ℤ, n ≠ 0 → polyToField (curve.toAffine.ψ n) ≠ 0
-- Exact first missing auxiliary (TauCeti Universal.lean):
--   polyEval_cusp_psi :
--     polyEval (cusp Z) 1 1 (curve.ψ n) = n.
-- It requires the cusp curve, W.specialize, Universal.polyEval and
-- Universal.ringEval, none of which are ported at the v4.32.2 pin.
-- With it, polyToField_psi_ne_zero follows by injectivity of
-- Universal.Ring -> Universal.Field and the cusp retraction as in TauCeti.
#check S1571UniversalPsiNonzero
#check polyToField
#check curve
end WeierstrassCurve.Universal
