/-
# B1 / O2: the `hb` obligation in "inclusion + explicit obligations" form

Consumer: the B1 branch lane.  `Mzk1G1PhiFixedLBranchSupportActual` consumes
`hb : Branch (hPolyL h hh) ⊆ boundarySetGlued`; this file reduces that obligation to the
inclusion of `branch_hPolyL_subset` plus explicit hypotheses, and records exactly what is
still open.

## What is proved here (no obligation)

* `branch_p1Inv_empty` : `Branch p1Inv = ∅`.  `p1Inv` is an involution
  (`Mzk1G1PsiP1InvBoundaryActual.p1Inv_inv`), hence an isomorphism, hence open
  immersion / locally of finite presentation / étale / smooth, so its branch locus is empty.
  The donor already contains the `IsIso ⇒ Smooth` engine: `ram_eq_empty_of_isIso`
  and `branch_eq_empty_of_isIso` (`Mzk1G1BelyiRamificationActual`), proved via
  `IsIso ⇒ IsOpenImmersion` (Mathlib `IsOpenImmersion.of_isIso`) and
  `IsOpenImmersion ⇒ LocallyOfFinitePresentation` / `Etale`.  Therefore **no**
  `smoothLocus p1Inv = ⊤`/`Ram p1Inv = ∅` parameter is needed: the task's fallback
  clause does not apply.

* `p1Inv_preimage_boundarySetGlued` : `p1Inv ⁻¹' boundarySetGlued = boundarySetGlued`,
  the preimage form of `p1Inv_mem_boundarySetGlued_iff` (donor).

## The inclusion (deliberately NOT an equality)

* `branch_hPolyL_subset` :
  `Branch (hPolyL h hh) ⊆ p1Inv '' Branch (hPoly h hh) ∪ Branch p1Inv`.
  Proof: `hPolyL = (p1Inv ≫ hPoly) ≫ p1Inv` (`hPolyL_def`), apply the donor
  `branch_comp_subset` twice (outer composite, then the inner `p1Inv ≫ hPoly`), and
  remove the empty term `p1Inv '' Branch p1Inv` via `branch_p1Inv_empty`.
  Per the task contract this file claims only the **inclusion**, not
  `Branch (hPolyL) = p1Inv '' Branch (hPoly)`: the equality is a different lane (O3(b),
  scheme-level `Branch (hPoly)` vs. critical values).  Note: the donor
  `branch_isIso_comp` / `branch_comp_isIso` would in fact give the equality; it is
  simply not the statement contracted here.

## The reduction (explicit-obligation form)

* `hb_of_branch_hPoly_subset` :
  `hbH : Branch (hPoly h hh) ⊆ p1Inv ⁻¹' boundarySetGlued` and
  `hbInv : Branch p1Inv ⊆ boundarySetGlued` imply
  `Branch (hPolyL h hh) ⊆ boundarySetGlued`.
  The `hbH`/`hbInv` inputs are kept as explicit parameters: they are the O2
  obligation shape, not disguised closure.
* `hbH_iff_branch_hPoly_subset` : `hbH` is *equivalent* to the plain
  `Branch (hPoly h hh) ⊆ boundarySetGlued` (boundary invariance of `p1Inv` +
  `p1Inv_image_subset_iff`).  So O2 is reduced **exactly** to the `hPoly` branch
  bound; nothing is hidden by the `p1Inv ⁻¹'` bookkeeping.
* `hb_of_branch_hPoly_subset_auto` : `hbInv` is free
  (`branch_p1Inv_empty`), so the only genuine input is `hbH`.

## Explicit obligations (NOT closed here)

* `[LocallyOfFinitePresentation (hPoly h hh)]` and
  `[LocallyOfFinitePresentation (hPolyL h hh)]` : no such instance exists in the tree (O4);
  carried as typeclass parameters, exactly as in `Mzk1G1PhiFixedLBranchSupportActual`.
  (`LocallyOfFinitePresentation p1Inv` itself needs no parameter: it is synthesized from
  `isIso_p1Inv`.)
* `hbH` (equivalently `Branch (hPoly h hh) ⊆ boundarySetGlued`) : O3(b) scheme
  layer + the analytic input (critical values of `h` in `{0,1}`); see
  `Mzk1G1B1ObligationsActual` O2/O3.  This file does not prove it.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiP1InvBoundaryActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 800000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1HbObligationsActual

open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual

/-! ## 0. `p1Inv` is an isomorphism -/

/-- `p1Inv` is an involution (`p1Inv_inv`), hence an isomorphism. -/
theorem isIso_p1Inv : IsIso p1Inv := ⟨p1Inv, p1Inv_inv, p1Inv_inv⟩

attribute [local instance] isIso_p1Inv

#print axioms isIso_p1Inv

/-! ## 1. The branch locus of `p1Inv` is empty -/

/-- **`p1Inv` does not ramify**: `Branch p1Inv = ∅`.

`p1Inv` is an isomorphism, so it is open immersion, locally of finite
presentation, étale and smooth; the donor `branch_eq_empty_of_isIso` turns this into
`Branch p1Inv = ∅`.  No explicit smoothness obligation is left. -/
theorem branch_p1Inv_empty : Branch p1Inv = ∅ :=
  branch_eq_empty_of_isIso p1Inv

#print axioms branch_p1Inv_empty

/-! ## 2. The inclusion for `hPolyL` -/

/-- **Branch inclusion for `hPolyL` (explicit-obligation shape)**:
`Branch (hPolyL h hh) ⊆ p1Inv '' Branch (hPoly h hh) ∪ Branch p1Inv`.

This is an inclusion, not an equality.  Writing `hPolyL = (p1Inv ≫ hPoly) ≫ p1Inv`, the
donor composition law `branch_comp_subset` is applied to the outer composite
`(p1Inv ≫ hPoly) ≫ p1Inv` and then to the inner composite `p1Inv ≫ hPoly`; the
term `p1Inv '' Branch p1Inv` is empty by `branch_p1Inv_empty`.

The `LocallyOfFinitePresentation` instances for `hPoly` and `hPolyL` are explicit
typeclass hypotheses (O4). -/
theorem branch_hPolyL_subset (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (hPolyL h hh)] :
    Branch (hPolyL h hh) ⊆ p1Inv '' Branch (hPoly h hh) ∪ Branch p1Inv := by
  -- outer composite: `Branch ((p1Inv ≫ hPoly) ≫ p1Inv) ⊆ p1Inv '' Branch (p1Inv ≫ hPoly) ∪ Branch p1Inv`
  have hstepA : Branch ((p1Inv ≫ hPoly h hh) ≫ p1Inv) ⊆
      p1Inv '' Branch (p1Inv ≫ hPoly h hh) ∪ Branch p1Inv :=
    branch_comp_subset (p1Inv ≫ hPoly h hh) p1Inv
  -- inner composite: `Branch (p1Inv ≫ hPoly) ⊆ hPoly '' Branch p1Inv ∪ Branch hPoly`
  have hstepB : Branch (p1Inv ≫ hPoly h hh) ⊆
      hPoly h hh '' Branch p1Inv ∪ Branch (hPoly h hh) :=
    branch_comp_subset p1Inv (hPoly h hh)
  -- `p1Inv` has empty branch locus
  have hempty : hPoly h hh '' Branch p1Inv = ∅ := by
    rw [branch_p1Inv_empty]
    exact Set.image_empty _
  -- hence `p1Inv '' Branch (p1Inv ≫ hPoly) ⊆ p1Inv '' Branch hPoly`
  have hsub : p1Inv '' Branch (p1Inv ≫ hPoly h hh) ⊆ p1Inv '' Branch (hPoly h hh) := by
    apply Set.image_mono
    intro z hz
    have hz' := hstepB hz
    rw [hempty, Set.empty_union] at hz'
    exact hz'
  calc
    Branch (hPolyL h hh) = Branch ((p1Inv ≫ hPoly h hh) ≫ p1Inv) := rfl
    _ ⊆ p1Inv '' Branch (hPoly h hh) ∪ Branch p1Inv :=
        hstepA.trans (Set.union_subset_union_left (Branch p1Inv) hsub)

#print axioms branch_hPolyL_subset

/-! ## 2.5 The preimage form of boundary invariance -/

/-- **`p1Inv` preserves the boundary, preimage form**:
`p1Inv ⁻¹' boundarySetGlued = boundarySetGlued`.

Pointwise this is `p1Inv_mem_boundarySetGlued_iff` (donor); it is the form used to
compare `hbH` with the plain boundary condition. -/
theorem p1Inv_preimage_boundarySetGlued :
    p1Inv ⁻¹' boundarySetGlued = boundarySetGlued := by
  ext y
  rw [Set.mem_preimage]
  exact p1Inv_mem_boundarySetGlued_iff y

#print axioms p1Inv_preimage_boundarySetGlued

/-! ## 3. The `hb` reduction -/

/-- **O2 reduction**: from `hbH` (the `hPoly` branch locus lands in the
`p1Inv`-preimage of the boundary) and `hbInv` (the `p1Inv` branch locus
lies in the boundary), deduce `Branch (hPolyL h hh) ⊆ boundarySetGlued`.

`hbH` is converted to `p1Inv '' Branch (hPoly) ⊆ boundary` with
`Set.image_subset_iff`, and `branch_hPolyL_subset` splits the `hPolyL` branch
locus into the two corresponding summands.  Both inputs are explicit hypotheses, not
discharged here. -/
theorem hb_of_branch_hPoly_subset (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (hPolyL h hh)]
    (hbH : Branch (hPoly h hh) ⊆ p1Inv ⁻¹' boundarySetGlued)
    (hbInv : Branch p1Inv ⊆ boundarySetGlued) :
    Branch (hPolyL h hh) ⊆ boundarySetGlued := by
  have h1 : p1Inv '' Branch (hPoly h hh) ⊆ boundarySetGlued :=
    Set.image_subset_iff.mpr hbH
  exact (branch_hPolyL_subset h hh).trans (Set.union_subset h1 hbInv)

#print axioms hb_of_branch_hPoly_subset

/-- **The remaining input `hbH` is exactly the `hPoly` branch bound**:
`Branch (hPoly h hh) ⊆ p1Inv ⁻¹' boundarySetGlued ↔ Branch (hPoly h hh) ⊆ boundarySetGlued`.

This records that the `p1Inv ⁻¹'` bookkeeping introduces no extra obligation: by
`p1Inv_image_subset_iff` and `Set.image_subset_iff`, `hbH` is literally the
`hPoly`-level branch bound (O3(b) scheme layer + analytic input, still open). -/
theorem hbH_iff_branch_hPoly_subset (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)] :
    Branch (hPoly h hh) ⊆ p1Inv ⁻¹' boundarySetGlued ↔
      Branch (hPoly h hh) ⊆ boundarySetGlued :=
  (Set.image_subset_iff (f := p1Inv) (s := Branch (hPoly h hh))).symm.trans
    (p1Inv_image_subset_iff _)

#print axioms hbH_iff_branch_hPoly_subset

/-- **`hbInv` is free**: the second input of `hb_of_branch_hPoly_subset` is
automatic because `Branch p1Inv = ∅`.  The only genuine O2 input is `hbH`. -/
theorem hb_of_branch_hPoly_subset_auto (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (hPolyL h hh)]
    (hbH : Branch (hPoly h hh) ⊆ p1Inv ⁻¹' boundarySetGlued) :
    Branch (hPolyL h hh) ⊆ boundarySetGlued := by
  refine hb_of_branch_hPoly_subset h hh hbH ?_
  rw [branch_p1Inv_empty]
  exact Set.empty_subset _

#print axioms hb_of_branch_hPoly_subset_auto

end LeanFormal.IUT.XiFPaper.Mzk1G1B1HbObligationsActual
