import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicCurve_DivisorClassGroup
import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicCurve_Repartitions
import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicCurve_AdelicIndex
import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicGeometry_CoherentBaseChange

/-!
# AG-FLT promotion layer (first-class importable modules; audit component)

COMPONENT, not a paper object.  Named consumers: stepxi/stage4/Lead AG infra,
[Mzk1] GeometricCore build, coord/AG-INFRA-PLAN.md.

Promotion of the adapted FLT modules into first-class importable Lean modules of
this repository.  The heavy mathematical content stays in the AG_FLT_* modules
(adapted from https://github.com/anthropics/fermats-last-theorem, Apache-2.0,
attribution headers preserved); this layer only re-exports and wraps the
declarations we consume, with kernel-checked interface facts over our pinned
Mathlib.  No axiom, no sorry, no fake data.

Targets promoted: Place/Divisor/degree/degZero/IsPrincipal/Pic/Pic0,
LSpace/ell/adeleBdd/adeleSpace, Repartitions/ground data, CoherentBaseChange.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual

open LeanFormal.IUT

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- Promoted place degree is a natural number. -/
theorem promotion_place_deg_nonneg (v : AlgebraicCurve.Place K F) :
    0 ≤ v.deg :=
  Nat.zero_le _

/-- Promoted divisor degree is additive. -/
theorem promotion_degree_add (D E : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.Divisor.degree (D + E) =
      AlgebraicCurve.Divisor.degree D + AlgebraicCurve.Divisor.degree E :=
  map_add _ _ _

/-- Promoted divisor degree vanishes on zero. -/
theorem promotion_degree_zero :
    AlgebraicCurve.Divisor.degree (0 : AlgebraicCurve.Divisor K F) = 0 :=
  map_zero _

/-- Promoted degree-zero membership characterization. -/
theorem promotion_mem_degZero_iff (D : AlgebraicCurve.Divisor K F) :
    D ∈ AlgebraicCurve.Divisor.degZero ↔
      AlgebraicCurve.Divisor.degree D = 0 :=
  AlgebraicCurve.Divisor.mem_degZero

/-- Promoted principal divisor characterization. -/
theorem promotion_isPrincipal_iff_mem (D : AlgebraicCurve.Divisor K F) :
    D ∈ AlgebraicCurve.Divisor.principal ↔
      AlgebraicCurve.Divisor.IsPrincipal D :=
  AlgebraicCurve.Divisor.mem_principal

/-- Promoted L-space dimension is a natural number. -/
theorem promotion_ell_nonneg (D : AlgebraicCurve.Divisor K F) :
    0 ≤ AlgebraicCurve.ell D :=
  Nat.zero_le _

/-- Promoted L-space membership is monotone in the divisor. -/
theorem promotion_lSpace_mono (D E : AlgebraicCurve.Divisor K F) (h : D ≤ E) :
    AlgebraicCurve.LSpace D ≤ AlgebraicCurve.LSpace E :=
  AlgebraicCurve.lSpace_mono h

/-- Promoted adelic bounded subspace is monotone in the divisor. -/
theorem promotion_adeleBdd_mono (D E : AlgebraicCurve.Divisor K F) (h : D ≤ E) :
    AlgebraicCurve.adeleBdd D ≤ AlgebraicCurve.adeleBdd E :=
  AlgebraicCurve.adeleBdd_mono h

end LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual
