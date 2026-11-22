import tmp.sheaf.xif.paper.AG_FLT_PromotionActual
import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicCurve_DivisorClassGroup
import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicCurve_AdelicIndex
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# AG06: line bundles / O(D) / divisor class group consumer (A-class reuse)

Bottom-up AG layer: consumes the promoted AG-FLT divisor/degree/Pic and adelic
index layers (complete proofs from the adapted FLT modules, Apache-2.0, namespaces
preserved; promotion layer AG_FLT_PromotionActual by qpilot).  No re-proof.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG06LineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual
open AlgebraicCurve

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- A place has nonnegative degree (reused complete proof). -/
theorem ag_place_deg_nonneg (v : Place K F) : 0 ≤ v.deg :=
  promotion_place_deg_nonneg v

/-- Divisor degree is additive (reused complete proof). -/
theorem ag_divisor_degree_add (D E : Divisor K F) :
    Divisor.degree (D + E) = Divisor.degree D + Divisor.degree E :=
  promotion_degree_add D E

/-- The zero divisor has degree zero (reused complete proof). -/
theorem ag_divisor_degree_zero :
    Divisor.degree (0 : Divisor K F) = 0 :=
  promotion_degree_zero

/-- Degree-zero membership characterization (reused complete proof). -/
theorem ag_mem_degZero_iff (D : Divisor K F) :
    D ∈ Divisor.degZero ↔ Divisor.degree D = 0 :=
  promotion_mem_degZero_iff D

/-- Principal divisors are exactly IsPrincipal (reused complete proof). -/
theorem ag_isPrincipal_iff_mem (D : Divisor K F) :
    D ∈ Divisor.principal ↔ Divisor.IsPrincipal D :=
  promotion_isPrincipal_iff_mem D

/-- L-space dimension is a natural number (reused complete proof). -/
theorem ag_ell_nonneg (D : Divisor K F) : 0 ≤ ell D :=
  promotion_ell_nonneg D

/-- L-spaces are monotone in the divisor (reused complete proof). -/
theorem ag_lSpace_mono (D E : Divisor K F) (h : D ≤ E) :
    LSpace D ≤ LSpace E :=
  promotion_lSpace_mono D E h

/-- Adelic bounded subspaces are monotone in the divisor (reused complete proof). -/
theorem ag_adeleBdd_mono (D E : Divisor K F) (h : D ≤ E) :
    adeleBdd D ≤ adeleBdd E :=
  promotion_adeleBdd_mono D E h

/-- A-class reuse record: (paper object, module, status). -/
def agLineBundleReuse : List (String × String × String) :=
  [ ("Place/Divisor/degree/degZero/IsPrincipal", "AG_FLT_Def_AlgebraicCurve_DivisorClassGroup (adapted FLT; Apache-2.0)", "A (complete proofs; promoted by qpilot)"),
    ("LSpace/ell/adeleBdd/adeleSpace", "AG_FLT_Def_AlgebraicCurve_AdelicIndex (adapted FLT)", "A (complete proofs; promoted)"),
    ("Repartitions/ground data", "AG_FLT_Def_AlgebraicCurve_Repartitions (adapted FLT)", "A (complete proofs)"),
    ("O(D) line-bundle model", "LSpace D = H0(O(D)); divisors modulo principal = Pic", "A interface (reuse); Riemann-Roch/Serrre pending port closure") ]

end LeanFormal.IUT.XiFPaper.AG06LineBundleActual

end
