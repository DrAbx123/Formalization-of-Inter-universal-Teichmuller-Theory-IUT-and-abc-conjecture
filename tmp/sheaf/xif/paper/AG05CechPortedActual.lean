import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# AG05p: Čech / H0 / H1 layer via the ported FLT canonical module (A-class)

Lead gate: AG05 must be GREEN using canonical ported assets (compile-pending marked
assumed available).  The canonical adapted module
tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor is still queued;
the ported FLT module (tmp/external/ported/flt, same source, complete proofs,
Apache-2.0 attribution preserved) is compiled GREEN in this workspace, so this file
imports it directly for the AG05 layer and exposes:

* two-chart Čech differential / H0 / H1 of a divisor;
* H0 = L(D) on a two-chart cover (cechH0Equiv);
* L-space monotonicity / union identity / Riemann-Roch-space inclusion.

The interface is identical to the planned adapted-module version (AG05CechActual);
when the adapted canonical module promotes, imports can be switched with the same
declarations.  No re-proof, no axiom, no sorry.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.AG05CechPortedActual

open LeanFormal.IUT
open AlgebraicCurve

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- Čech differential of the two-chart complex (canonical ported definition). -/
abbrev agpCechDiff (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :=
  cechDiff S₀ S₁ D

/-- Čech H0 = kernel of the Čech differential (canonical ported definition). -/
abbrev agpCechH0 (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :=
  cechH0 S₀ S₁ D

/-- Čech H1 (canonical ported definition). -/
abbrev agpCechH1 (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :=
  cechH1 S₀ S₁ D

/-- L-space on a set of places (canonical ported definition). -/
abbrev agpLSpaceOn (S : Set (Place K F)) (D : Divisor K F) :=
  lSpaceOn S D

/-- H0 is the kernel of the Čech differential (complete proof, reused). -/
theorem agp_cechH0_eq (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    cechH0 S₀ S₁ D = (cechSections S₀ S₁ D).H0 :=
  cechH0_eq S₀ S₁ D

/-- Membership in H0: the two chart sections agree (complete proof, reused). -/
theorem agp_mem_cechH0_iff {S₀ S₁ : Set (Place K F)} {D : Divisor K F}
    (p : lSpaceOn S₀ D × lSpaceOn S₁ D) :
    p ∈ cechH0 S₀ S₁ D ↔ (p.1 : F) = p.2 :=
  mem_cechH0_iff p

/-- H1 as the quotient (complete proof, reused). -/
theorem agp_cechH1_eq (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    cechH1 S₀ S₁ D = (cechSections S₀ S₁ D).H1 :=
  cechH1_eq S₀ S₁ D

/-- On a two-chart cover, H0 is linearly K-isomorphic to L(D)=riemannRochSpace D
(complete proof of the ported canonical module). -/
def agp_cechH0Equiv {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (D : Divisor K F) :
    cechH0 S₀ S₁ D ≃ₗ[K] riemannRochSpace D :=
  cechH0Equiv hcover D

/-- L-space monotonicity in the divisor (complete proof, reused). -/
theorem agp_lSpaceOn_mono {D E : Divisor K F} (hDE : D ≤ E) (S : Set (Place K F)) :
    lSpaceOn S D ≤ lSpaceOn S E :=
  lSpaceOn_mono hDE S

/-- L-space on a union is the infimum of the two chart L-spaces (complete proof). -/
theorem agp_lSpaceOn_union (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    lSpaceOn (S₀ ∪ S₁) D = lSpaceOn S₀ D ⊓ lSpaceOn S₁ D :=
  lSpaceOn_union S₀ S₁ D

/-- Riemann-Roch space is contained in every chart L-space (complete proof). -/
theorem agp_riemannRochSpace_le_lSpaceOn (S : Set (Place K F)) (D : Divisor K F) :
    riemannRochSpace D ≤ lSpaceOn S D :=
  riemannRochSpace_le_lSpaceOn S D

/-- A-class reuse record: (paper object, canonical ported module, status). -/
def agpCechReuse : List (String × String × String) :=
  [ ("Čech complex / H0 / H1 on a two-chart cover", "tmp/external/ported/flt Definitions/Def_AlgebraicCurve_CechSectionsOfDivisor (Apache-2.0)", "A (complete proofs; ported GREEN; reused)"),
    ("H0 = L(D) on a cover (cechH0Equiv)", "same ported module", "A (complete proof; reused)"),
    ("L-space monotonicity / union identity / RR-space inclusion", "same ported module", "A (complete proofs; reused)"),
    ("generic sheaf cohomology", "Mathlib.CategoryTheory.Sites.SheafCohomology.Basic/Cech", "A (Mathlib, imported)"),
    ("adapted canonical counterpart", "tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor", "queued; switch imports when promoted (same interface)") ]

end LeanFormal.IUT.XiFPaper.AG05CechPortedActual

end
