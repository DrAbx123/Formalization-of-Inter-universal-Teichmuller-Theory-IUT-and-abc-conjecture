import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChartInfBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChart0BoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1InvActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyFinalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import tmp.sheaf.xif.paper.Mzk1G1BelyiRamificationActual
import Mathlib.Tactic

/-!
# B1 (hψ reduction): `p1Inv` preserves the Belyi boundary, and `hPolyL` reduces to `hPoly`

Consumers: the B1 branch lane.  `phiFixedL = psiFixed ≫ hPolyL` with
`hPolyL = p1Inv ≫ hPoly ≫ p1Inv` (`Mzk1G1PsiHPolyLambdaActual.hPolyL_def`).  The branch
obligation of `hψ` is stated for `hPolyL` (`hPolyL h hh '' Branch (psiFixed n T) ⊆ {0,1,∞}`),
while the t-chart dictionary that is actually available on the pieces of `Y_n`
(`Mzk1G1PhiFixedLChartInfBoundaryActual.psiFixed_comp_hPoly_qPiece_mem_boundary_iff`) is
stated for `hPoly` itself.  This file supplies the missing bridge:

* `p1Inv_mem_boundarySetGlued_iff` : the inversion `lambda |-> lambda^{-1}` of `P^1`
  (glued morphism `p1Inv`, `Mzk1G1PsiP1InvActual`) keeps the boundary
  `{0, 1, infinity}`.  Geometrically `p1Inv` swaps `0` and `infinity` and fixes `1`; the
  proof does not need that description, only the two chart dictionaries:
  on the lambda chart `p1Inv` acts as `chartMorphismInf X` (donor `p1Inv_ι_false`), and on
  the t-chart it acts as `chartMorphism0 X` (donor `p1Inv_ι_true`), so both sides of the
  equivalence are the same ring condition `X ∈ p or X - 1 ∈ p`
  (`chartMorphismInf_mem_boundarySetGlued_iff`, `chartMorphism0_mem_boundarySetGlued_iff`).
  No chart-intersection (overlap) analysis is needed.
* `p1Inv_inv` : `p1Inv ≫ p1Inv = 1`.  Proved by `Scheme.OpenCover.hom_ext` on the two-chart
  open cover: it suffices that each chart piece composed with `p1Inv ≫ p1Inv` is the piece
  itself, which is the two chart formulas above together with `evalAt X = id`.
* `p1Inv_image_subset_iff` : for every point set `S`,
  `p1Inv '' S ⊆ boundarySetGlued <-> S ⊆ boundarySetGlued` (the point-set form of the
  boundary preservation; the consumer substitutes `S = Branch`-images).
* `p1Inv_image_boundarySetGlued` : `p1Inv '' boundarySetGlued = boundarySetGlued`.
* `hPolyL_apply`, `hPolyL_image_eq`, `hPolyL_image_boundary_iff`,
  `hPolyL_branch_image_boundary_iff` : the reduction of the `hψ` obligation from the
  `hPolyL` form to the `hPoly` form:
  `hPolyL h hh '' S ⊆ {0,1,infinity} <-> hPoly h hh '' (p1Inv '' S) ⊆ {0,1,infinity}`,
  in particular for `S = Branch (psiFixed n T)`.

## Degradation note (per the task's fallback clause)

The consumer-facing statement is given for an ARBITRARY point set `S`
(`hPolyL_image_boundary_iff`), because the set `Branch (psiFixed n T)` of the branch lane
requires a `LocallyOfFinitePresentation (psiFixed n T)` instance which this file does not
manufacture (there is no such instance in the tree); `hPolyL_branch_image_boundary_iff`
therefore carries that instance as an explicit hypothesis.  Nothing else is weakened.

No sorry, no admit, no new axioms.
-/

noncomputable section
set_option maxHeartbeats 800000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvBoundaryActual

open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChartInfBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChart0BoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.BelyiRamification

/-! ## 1. The chart self-maps at the coordinate `X` are the chart inclusions

`chartMorphism0 a` is `Spec Q[lambda] -> P^1` sending `lambda` to `a`; at `a = X` (in the
coefficient ring `Q[lambda]` itself) this is just the inclusion of the lambda chart, and
likewise for the t-chart. -/

/-- Evaluation at the polynomial `X` is the identity of `Q[X]`. -/
theorem evalAt_X_eq_id :
    evalAt (R := Polynomial ℚ) Polynomial.X = RingHom.id (Polynomial ℚ) :=
  RingHom.ext (fun p => by simpa using evalAt_X_self p)

/-- `chartMorphism0 X` is the lambda chart of `P^1`. -/
theorem chartMorphism0_X_eq_localChart0 :
    chartMorphism0 (R := Polynomial ℚ) Polynomial.X = localChart0 := by
  rw [chartMorphism0, evalAt_X_eq_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- `chartMorphismInf X` is the t-chart of `P^1`. -/
theorem chartMorphismInf_X_eq_localChartInf :
    chartMorphismInf (R := Polynomial ℚ) Polynomial.X = localChartInf := by
  rw [chartMorphismInf, evalAt_X_eq_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- Point form of `chartMorphism0_X_eq_localChart0`. -/
theorem chartMorphism0_X_apply (p : PrimeSpectrum (Polynomial ℚ)) :
    chartMorphism0 (R := Polynomial ℚ) Polynomial.X p = localChart0.base p :=
  congrArg (fun g : chart0Scheme ⟶ projectiveLineGlued => g p) chartMorphism0_X_eq_localChart0

/-- Point form of `chartMorphismInf_X_eq_localChartInf`. -/
theorem chartMorphismInf_X_apply (q : PrimeSpectrum (Polynomial ℚ)) :
    chartMorphismInf (R := Polynomial ℚ) Polynomial.X q = localChartInf.base q :=
  congrArg (fun g : chartInfScheme ⟶ projectiveLineGlued => g q)
    chartMorphismInf_X_eq_localChartInf

#print axioms evalAt_X_eq_id
#print axioms chartMorphism0_X_eq_localChart0
#print axioms chartMorphismInf_X_eq_localChartInf
#print axioms chartMorphism0_X_apply
#print axioms chartMorphismInf_X_apply

/-! ## 2. The chart formulas of `p1Inv`, with the chart inclusions named -/

/-- `p1Inv` on the lambda chart: `p1Inv_ι_false`, restated with `localChart0`. -/
theorem localChart0_comp_p1Inv :
    localChart0 ≫ p1Inv = chartMorphismInf (R := Polynomial ℚ) Polynomial.X :=
  p1Inv_ι_false

/-- `p1Inv` on the t-chart: `p1Inv_ι_true`, restated with `localChartInf`. -/
theorem localChartInf_comp_p1Inv :
    localChartInf ≫ p1Inv = chartMorphism0 (R := Polynomial ℚ) Polynomial.X :=
  p1Inv_ι_true

/-- The lambda chart, transported by `p1Inv`, is the t-chart point of coordinate `X`. -/
theorem p1Inv_localChart0_apply (p : PrimeSpectrum (Polynomial ℚ)) :
    p1Inv (localChart0.base p) = chartMorphismInf (R := Polynomial ℚ) Polynomial.X p := by
  rw [← Scheme.Hom.comp_apply localChart0 p1Inv p, localChart0_comp_p1Inv]

/-- The t-chart, transported by `p1Inv`, is the lambda-chart point of coordinate `X`. -/
theorem p1Inv_localChartInf_apply (q : PrimeSpectrum (Polynomial ℚ)) :
    p1Inv (localChartInf.base q) = chartMorphism0 (R := Polynomial ℚ) Polynomial.X q := by
  rw [← Scheme.Hom.comp_apply localChartInf p1Inv q, localChartInf_comp_p1Inv]

#print axioms localChart0_comp_p1Inv
#print axioms localChartInf_comp_p1Inv
#print axioms p1Inv_localChart0_apply
#print axioms p1Inv_localChartInf_apply

/-! ## 3. `p1Inv` is an involution

Both chart pieces composed with `p1Inv ≫ p1Inv` are the pieces themselves; by the sheaf
property of the two-chart open cover of `P^1` (`Scheme.OpenCover.hom_ext`) this is the
identity. -/

/-- `chartMorphismInf X ≫ p1Inv` is the lambda chart. -/
theorem chartMorphismInf_X_comp_p1Inv :
    chartMorphismInf (R := Polynomial ℚ) Polynomial.X ≫ p1Inv = localChart0 := by
  rw [chartMorphismInf_comp_p1Inv, chartMorphism0_X_eq_localChart0]

/-- `chartMorphism0 X ≫ p1Inv` is the t-chart. -/
theorem chartMorphism0_X_comp_p1Inv :
    chartMorphism0 (R := Polynomial ℚ) Polynomial.X ≫ p1Inv = localChartInf := by
  rw [chartMorphism0_X_eq_localChart0, localChart0_comp_p1Inv, chartMorphismInf_X_eq_localChartInf]

/-- The chart pieces `p1InvFun i` of `p1Inv`, composed with `p1Inv`, give back the pieces of
the two-chart cover of `P^1`. -/
theorem p1InvFun_comp_p1Inv (i : p1GlueData.J) : p1InvFun i ≫ p1Inv = p1GlueData.ι i := by
  obtain ⟨b⟩ := i
  cases b
  · exact chartMorphismInf_X_comp_p1Inv
  · exact chartMorphism0_X_comp_p1Inv

/-- **`p1Inv` is an involution**: `p1Inv ≫ p1Inv = 1`. -/
theorem p1Inv_inv : p1Inv ≫ p1Inv = 𝟙 projectiveLineGlued := by
  apply Scheme.Cover.hom_ext p1GlueData.openCover
  intro i
  show p1GlueData.ι i ≫ (p1Inv ≫ p1Inv) = p1GlueData.ι i ≫ 𝟙 projectiveLineGlued
  rw [← Category.assoc]
  rw [p1Inv_ι i, p1InvFun_comp_p1Inv, Category.comp_id]

/-- Point form of `p1Inv_inv`. -/
theorem p1Inv_apply_p1Inv (y : projectiveLineGlued) : p1Inv (p1Inv y) = y := by
  have h : (p1Inv ≫ p1Inv) y = (𝟙 projectiveLineGlued) y := by rw [p1Inv_inv]
  rw [Scheme.Hom.comp_apply] at h
  simpa using h

#print axioms chartMorphismInf_X_comp_p1Inv
#print axioms chartMorphism0_X_comp_p1Inv
#print axioms p1InvFun_comp_p1Inv
#print axioms p1Inv_inv
#print axioms p1Inv_apply_p1Inv

/-! ## 4. `p1Inv` preserves the Belyi boundary `{0, 1, infinity}`

`p1Inv` swaps `0` and `infinity` and fixes `1`; it is enough to compare the ring conditions
read on the two charts. -/

/-- **Boundary preservation (pointwise).**  The inversion of `P^1` keeps `{0, 1, infinity}`:
on the lambda chart it is the t-chart morphism at `X` and on the t-chart it is the
lambda-chart morphism at `X`, so both sides of the equivalence are `X in p or X - 1 in p`. -/
theorem p1Inv_mem_boundarySetGlued_iff (y : projectiveLineGlued) :
    p1Inv y ∈ boundarySetGlued ↔ y ∈ boundarySetGlued := by
  rcases localChart_jointly_surjective y with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · have h1 : p1Inv (localChart0.base p) ∈ boundarySetGlued ↔
        (Polynomial.X ∈ p.asIdeal ∨ Polynomial.X - 1 ∈ p.asIdeal) := by
      rw [p1Inv_localChart0_apply p]
      exact chartMorphismInf_mem_boundarySetGlued_iff _ p
    have h2 : localChart0.base p ∈ boundarySetGlued ↔
        (Polynomial.X ∈ p.asIdeal ∨ Polynomial.X - 1 ∈ p.asIdeal) := by
      rw [← chartMorphism0_X_apply p]
      exact chartMorphism0_mem_boundarySetGlued_iff _ p
    exact h1.trans h2.symm
  · have h1 : p1Inv (localChartInf.base q) ∈ boundarySetGlued ↔
        (Polynomial.X ∈ q.asIdeal ∨ Polynomial.X - 1 ∈ q.asIdeal) := by
      rw [p1Inv_localChartInf_apply q]
      exact chartMorphism0_mem_boundarySetGlued_iff _ q
    have h2 : localChartInf.base q ∈ boundarySetGlued ↔
        (Polynomial.X ∈ q.asIdeal ∨ Polynomial.X - 1 ∈ q.asIdeal) := by
      rw [← chartMorphismInf_X_apply q]
      exact chartMorphismInf_mem_boundarySetGlued_iff _ q
    exact h1.trans h2.symm

/-- **Boundary preservation (for arbitrary point sets).**  A point set `S` is contained in
`{0, 1, infinity}` exactly when its image under `p1Inv` is.  This is the form to be consumed
by the branch lane with `S` a `Branch` image. -/
theorem p1Inv_image_subset_iff (S : Set projectiveLineGlued) :
    p1Inv '' S ⊆ boundarySetGlued ↔ S ⊆ boundarySetGlued := by
  constructor
  · intro h y hy
    exact (p1Inv_mem_boundarySetGlued_iff y).mp (h ⟨y, hy, rfl⟩)
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact (p1Inv_mem_boundarySetGlued_iff y).mpr (h hy)

/-- `p1Inv` maps the boundary onto itself. -/
theorem p1Inv_image_boundarySetGlued :
    p1Inv '' boundarySetGlued = boundarySetGlued := by
  refine Set.Subset.antisymm ?_ ?_
  · exact (p1Inv_image_subset_iff boundarySetGlued).mpr (fun _ h => h)
  · intro z hz
    exact ⟨p1Inv z, (p1Inv_mem_boundarySetGlued_iff z).mpr hz, p1Inv_apply_p1Inv z⟩

#print axioms p1Inv_mem_boundarySetGlued_iff
#print axioms p1Inv_image_subset_iff
#print axioms p1Inv_image_boundarySetGlued

/-! ## 5. Reduction of the `hψ` obligation from `hPolyL` to `hPoly`

`hPolyL = p1Inv ≫ hPoly ≫ p1Inv`, so on points `hPolyL y = p1Inv (hPoly (p1Inv y))`; the
boundary preservation of section 4 removes the outer `p1Inv` and moves the inner one into
the source set. -/

/-- Point formula of `hPolyL`. -/
theorem hPolyL_apply (h : Polynomial ℚ) (hh : h ≠ 0) (y : projectiveLineGlued) :
    hPolyL h hh y = p1Inv (hPoly h hh (p1Inv y)) := by
  simp only [hPolyL_def, Scheme.Hom.comp_apply]

/-- The image of `hPolyL` on `S` is the image of `hPoly` on the `p1Inv`-image of `S`, pushed
forward once more by `p1Inv`. -/
theorem hPolyL_image_eq (h : Polynomial ℚ) (hh : h ≠ 0) (S : Set projectiveLineGlued) :
    hPolyL h hh '' S = p1Inv '' (hPoly h hh '' (p1Inv '' S)) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hPoly h hh (p1Inv y), ⟨p1Inv y, ⟨y, hy, rfl⟩, rfl⟩, (hPolyL_apply h hh y).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hw
    obtain ⟨y, hy, rfl⟩ := hu
    exact ⟨y, hy, hPolyL_apply h hh y⟩

/-- **The `hψ` reduction**: the `hPolyL` form of the boundary obligation is equivalent to
the `hPoly` form on the `p1Inv`-image of the source set. -/
theorem hPolyL_image_boundary_iff (h : Polynomial ℚ) (hh : h ≠ 0)
    (S : Set projectiveLineGlued) :
    hPolyL h hh '' S ⊆ boundarySetGlued ↔
      hPoly h hh '' (p1Inv '' S) ⊆ boundarySetGlued := by
  rw [hPolyL_image_eq h hh S]
  exact p1Inv_image_subset_iff _

/-- The same reduction at the branch set `Branch (psiFixed n T)` actually used by the B1
lane.  The finite-presentation instance is an explicit hypothesis: no such instance for
`psiFixed n T` exists in the tree, and this file does not manufacture one (see the header). -/
theorem hPolyL_branch_image_boundary_iff (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) [LocallyOfFinitePresentation (psiFixed n T)] :
    hPolyL h hh '' Branch (psiFixed n T) ⊆ boundarySetGlued ↔
      hPoly h hh '' (p1Inv '' Branch (psiFixed n T)) ⊆ boundarySetGlued :=
  hPolyL_image_boundary_iff h hh _

#print axioms hPolyL_apply
#print axioms hPolyL_image_eq
#print axioms hPolyL_image_boundary_iff
#print axioms hPolyL_branch_image_boundary_iff

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvBoundaryActual
