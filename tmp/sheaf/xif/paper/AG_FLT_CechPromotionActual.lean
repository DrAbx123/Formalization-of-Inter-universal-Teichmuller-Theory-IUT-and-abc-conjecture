import tmp.sheaf.xif.paper.AG_FLT_CechSectionsActual
import tmp.sheaf.xif.paper.AG_FLT_TwoChartCechActual
import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicCurve_AdelicIndex

/-!
# AG-FLT Cech promotion layer (first-class importable modules; audit component)

COMPONENT, not a paper object.  Named consumers: stepxi AG05CechActual, stage4,
Lead AG-INFRA-PLAN; [Mzk1] GeometricCore build (Cech H0/H1 layer).

Promotes the adapted FLT Cech-of-divisor layer into first-class importable
modules: two-chart Cech complex, Cech H0/H1 of a divisor line bundle, the Cech
H0/H1/L-space comparison lemmas.  Attribution: adapted from
https://github.com/anthropics/fermats-last-theorem (Apache-2.0) - see headers in
AG_FLT_CechSectionsActual / AG_FLT_TwoChartCechActual / AG_FLT_Def_AlgebraicCurve_*.
All promoted declarations have COMPLETE proofs in the adapted modules (no sorry;
probe trio).  No axiom/fake data.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AG_FLT_CechPromotionActual

open LeanFormal.IUT

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- Cech H0 is a kernel of the Cech differential. -/
theorem promotion_cechH0_eq (S₀ S₁ : Set (AlgebraicCurve.Place K F))
    (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.cechH0 S₀ S₁ D =
      LinearMap.ker (AlgebraicCurve.cechDiff S₀ S₁ D) :=
  AlgebraicCurve.cechH0_eq S₀ S₁ D

/-- Cech H1 is the cokernel of the Cech differential. -/
theorem promotion_cechH1_eq (S₀ S₁ : Set (AlgebraicCurve.Place K F))
    (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.cechH1 S₀ S₁ D =
      ((AlgebraicCurve.lSpaceOn (S₀ ∩ S₁) D) ⧸
        LinearMap.range (AlgebraicCurve.cechDiff S₀ S₁ D)) :=
  AlgebraicCurve.cechH1_eq S₀ S₁ D

/-- The L-space of a divisor injects into the two-chart Cech H0. -/
theorem promotion_riemannRochSpace_le_lSpaceOn (S : Set (AlgebraicCurve.Place K F))
    (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.LSpace D ≤ AlgebraicCurve.lSpaceOn S D :=
  AlgebraicCurve.riemannRochSpace_le_lSpaceOn S D

/-- lSpaceOn is monotone in the divisor. -/
theorem promotion_lSpaceOn_mono {D E : AlgebraicCurve.Divisor K F} (hDE : D ≤ E)
    (S : Set (AlgebraicCurve.Place K F)) :
    AlgebraicCurve.lSpaceOn S D ≤ AlgebraicCurve.lSpaceOn S E :=
  AlgebraicCurve.lSpaceOn_mono hDE S

/-- lSpaceOn of the union is the intersection. -/
theorem promotion_lSpaceOn_union (S₀ S₁ : Set (AlgebraicCurve.Place K F))
    (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.lSpaceOn (S₀ ∪ S₁) D =
      AlgebraicCurve.lSpaceOn S₀ D ⊓ AlgebraicCurve.lSpaceOn S₁ D :=
  AlgebraicCurve.lSpaceOn_union S₀ S₁ D

end LeanFormal.IUT.XiFPaper.AG_FLT_CechPromotionActual
