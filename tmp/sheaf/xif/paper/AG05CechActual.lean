import tmp.sheaf.xif.paper.AG_FLT_CechPromotionActual
import tmp.sheaf.xif.paper.AG_FLT_CechSectionsActual
import tmp.sheaf.xif.paper.AG_FLT_TwoChartCechActual
import tmp.sheaf.xif.paper.AG_FLT_PromotionActual
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# AG05: Čech / H0 / H1 layer for curves (canonical qpilot promotion; COMPLETE proofs)

Lead gate (e): AG05 must be a complete-proof layer using the canonical Čech modules
delivered by qpilot (checker-CITABLE, complete proofs, Apache-2.0 attribution in the
adapted sources):
* tmp.sheaf.xif.paper.AG_FLT_CechPromotionActual (primary; 5 promoted declarations);
* tmp.sheaf.xif.paper.AG_FLT_CechSectionsActual (lSpaceOn / cechDiff / cechH0 / cechH1 /
  cechH0Equiv / H1 laws);
* tmp.sheaf.xif.paper.AG_FLT_TwoChartCechActual (two-chart Čech complex);
* tmp.sheaf.xif.paper.AG_FLT_PromotionActual (divisor/degree/ell/adelic layer).
Mathlib.CategoryTheory.Sites.SheafCohomology.Basic/Cech imported as generic substrate.

This file is the AG05 consumer interface: Čech differential / H0 / H1 of a divisor,
H0 = L(D) on a two-chart cover, L-space monotonicity/union identity, and the
Riemann-Roch-space inclusion.  All proofs are complete (reused from the canonical
promoted layer); no re-proof, no axiom, no sorry.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.AG05CechActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.AG_FLT_CechPromotionActual
open AlgebraicCurve

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- Čech differential of the two-chart complex (canonical definition). -/
abbrev agCechDiff (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :=
  cechDiff S₀ S₁ D

/-- Čech H0 (canonical definition). -/
abbrev agCechH0 (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :=
  cechH0 S₀ S₁ D

/-- Čech H1 (canonical definition). -/
abbrev agCechH1 (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :=
  cechH1 S₀ S₁ D

/-- H0 is the kernel of the Čech differential (promoted complete proof). -/
theorem ag_cechH0_eq (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    cechH0 S₀ S₁ D = LinearMap.ker (cechDiff S₀ S₁ D) :=
  promotion_cechH0_eq S₀ S₁ D

/-- H1 as the quotient of the intersection L-space by the Čech differential range
(promoted complete proof). -/
theorem ag_cechH1_eq (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    cechH1 S₀ S₁ D = (lSpaceOn (S₀ ∩ S₁) D ⧸ LinearMap.range (cechDiff S₀ S₁ D)) :=
  promotion_cechH1_eq S₀ S₁ D

/-- Membership in H0: the two chart sections agree (complete proof, canonical). -/
theorem ag_mem_cechH0_iff {S₀ S₁ : Set (Place K F)} {D : Divisor K F}
    (p : lSpaceOn S₀ D × lSpaceOn S₁ D) :
    p ∈ cechH0 S₀ S₁ D ↔ (p.1 : F) = p.2 :=
  mem_cechH0_iff p

/-- On a two-chart cover, H0 is linearly K-isomorphic to L(D)=riemannRochSpace D
(complete proof, canonical). -/
def ag_cechH0Equiv {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (D : Divisor K F) :
    cechH0 S₀ S₁ D ≃ₗ[K] riemannRochSpace D :=
  cechH0Equiv hcover D

/-- The Riemann-Roch space L(D) injects into every chart L-space (promoted). -/
theorem ag_riemannRochSpace_le_lSpaceOn (S : Set (Place K F)) (D : Divisor K F) :
    LSpace D ≤ lSpaceOn S D :=
  promotion_riemannRochSpace_le_lSpaceOn S D

/-- L-space monotonicity in the divisor (promoted complete proof). -/
theorem ag_lSpaceOn_mono {D E : Divisor K F} (hDE : D ≤ E) (S : Set (Place K F)) :
    lSpaceOn S D ≤ lSpaceOn S E :=
  promotion_lSpaceOn_mono hDE S

/-- L-space on a union is the infimum of the two chart L-spaces (promoted). -/
theorem ag_lSpaceOn_union (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    lSpaceOn (S₀ ∪ S₁) D = lSpaceOn S₀ D ⊓ lSpaceOn S₁ D :=
  promotion_lSpaceOn_union S₀ S₁ D

/-- A-class reuse record: (paper object, canonical module, status). -/
def agCechReuse : List (String × String × String) :=
  [ ("Čech complex / H0 / H1 on a two-chart cover", "AG_FLT_TwoChartCechActual + AG_FLT_CechSectionsActual", "A (complete proofs; canonical qpilot)"),
    ("promoted Cech laws (H0=ker, H1=quotient, L(D)<=lSpaceOn, mono, union)", "AG_FLT_CechPromotionActual (5 decls; checker CITABLE)", "A (complete proofs; promoted)"),
    ("divisor/degree/ell/adelic layer", "AG_FLT_PromotionActual + adapted DivisorClassGroup/AdelicIndex (CITABLE)", "A (complete proofs)"),
    ("generic sheaf cohomology", "Mathlib.CategoryTheory.Sites.SheafCohomology.Basic/Cech", "A (Mathlib)") ]

end LeanFormal.IUT.XiFPaper.AG05CechActual

end
