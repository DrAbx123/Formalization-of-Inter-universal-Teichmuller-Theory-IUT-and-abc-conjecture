/-
# B1 (owner emmy lane): the **lambda-chart value dictionary** for `phiFixedL`

The scheme-level branch statement of B1 lives in
`Mzk1G1PhiFixedLBranchSupportActual.phiFixedL_branch_subset` (grace's
`BelyiRamification.Branch`, composition law `branch_comp_subset`).  Its inputs are statements
about *points of `P^1`*, while the analytic data (`Mzk1G1PsiBranchSetActual`,
`Mzk1G1PsiM2AnalyticActual`) is data about *values*.  This file supplies the missing
scheme<->value bridge on the lambda chart, so those inputs -- and the avoidance statements of
the B1/B2 lanes -- reduce to ring-membership conditions in `R n`.

## What is proved (unconditional, no sorry/axiom)

1. `chartMorphism0_mem_boundarySetGlued_iff` (general base ring `R`): a lambda-chart point
   with value `a` lies in `boundarySetGlued = p1Zero ∪ p1One ∪ p1Infinity` iff `a ∈ p` or
   `a - 1 ∈ p`.  The infinite slot cannot occur in the lambda chart
   (`chartMorphism0_not_mem_p1Infinity`); the two finite slots are the judge lemmas
   `chartMorphism0_mem_p1Zero_iff` / `chartMorphism0_mem_p1One_iff`.
2. `evalAt_apply_aeval`: `evalAt a q = Polynomial.aeval a q` definitionally (this is why the
   dictionary below can be stated with `Polynomial.aeval`, the notation of the value-level
   middleware; proof is `rfl`).
3. `phiFixedL_chart0_point_eq`: on the first chart of `Y_n`, `phiFixedL` is the lambda-chart
   point of coordinate `h(u)`, `u = psiChart0Coord n T` (point form of
   `phiFixedL_chart0_eq` of `Mzk1G1PhiFixedLChart0Actual`).
4. The four value/boundary dictionaries of the first chart:
   `phiFixedL_chart0_point_mem_p1Zero_iff`, `..._mem_p1One_iff`, `..._mem_boundary_iff` and
   `..._notMem_boundary_iff` (the last one is the ring-level form of the `AvoidsBoundary`
   obligations).
5. `phiFixedL_chart0_ram_mem_boundary_of_value`: **the reduction used by the branch lane** --
   if every first-chart ramification point `p` of `phiFixedL` satisfies "`h(u)` or
   `h(u) - 1` vanishes at `p`", then its image lies in `{0, 1, ∞}`.  So the point-level
   obligation of a branch input becomes a *ring* condition on `R n`; no `ℂ`-valued downgrade.

## Deliberately not done here

* The scheme-level branch containment itself is **not** restated: it is
  `Mzk1G1PhiFixedLBranchSupportActual.phiFixedL_branch_subset`, kept in one place (a second
  file with the same content under another name was deprecated by the lane owner on
  2026-11-17 08:17; see `dag/watchdog/emmy-backup/`).
* The second (t-)chart dictionary is not available in the tree; that is the remaining gap for
  placing `hPolyL h hh '' Branch (psiFixed n T)` in the boundary at the level of schemes.
* `Mzk1G1B1TAvoidFinalActual` (the `D_T` unit computation) is not imported: it does not
  compile in the current tree, so its lemmas are unusable (and its `#print axioms` output
  currently shows `sorryAx`).  The dictionary above is exactly the ingredient that its
  avoidance statements need, so they can be rebased on this file once it is repaired.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1BelyiRamificationActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaFactsActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChart0Actual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLInfinityActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1ZeroJudgeActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1OneJudgeActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChart0BoundaryActual

open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1OneJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChart0Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLInfinityActual

/-! ## 1. The lambda-chart boundary dictionary (general base ring) -/

/-- **Lambda-chart boundary dictionary.**  A lambda-chart point with value `a` lies on the
Belyi boundary `{0, 1, ∞}` of `P^1` exactly when `a` vanishes or equals `1` at the prime `p`:
the point `∞` is never a lambda-chart point, and the `0`/`1` slots are read off by the judge
lemmas. -/
theorem chartMorphism0_mem_boundarySetGlued_iff {R : Type} [CommRing R] [Algebra ℚ R]
    (a : R) (p : PrimeSpectrum R) :
    chartMorphism0 a p ∈ boundarySetGlued ↔ (a ∈ p.asIdeal ∨ a - 1 ∈ p.asIdeal) := by
  simp only [boundarySetGlued, Set.mem_union, chartMorphism0_mem_p1Zero_iff,
    chartMorphism0_mem_p1One_iff]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (chartMorphism0_not_mem_p1Infinity (R := R) a p)
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

/-- `evalAt a q` is `Polynomial.aeval a q` (definitionally; `evalAt = (aeval a).toRingHom`).
This lets the dictionaries below be stated in the `aeval` notation of the value-level
middleware while being proved with the point formulas of
`Mzk1G1ProjectiveLineTransitionActual`. -/
theorem evalAt_apply_aeval {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    (q : Polynomial ℚ) : evalAt a q = Polynomial.aeval a q := rfl

/-! ## 2. The first chart of `phiFixedL` -/

/-- **The first chart of `Y_n` under `phiFixedL`** (point form of `phiFixedL_chart0_eq`): the
point attached to `p` is sent to the lambda-chart point of coordinate `h(u)`,
`u = psiChart0Coord n T`. -/
theorem phiFixedL_chart0_point_eq (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (p : PrimeSpectrum (R n)) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base p) =
      chartMorphism0 (R := R n) (evalAt (R := R n) (psiChart0Coord n T) h) p := by
  have hx := congrArg (fun g : fermatChart0Scheme n ⟶ projectiveLineGlued => g p)
    (phiFixedL_chart0_eq n T h hh)
  rw [Scheme.Hom.comp_apply] at hx
  simpa using hx

/-! ## 3. The four value/boundary dictionaries of the first chart -/

/-- **Dictionary, `0`**: the first-chart point attached to `p` maps to `0` iff `h(u)` vanishes
at `p`. -/
theorem phiFixedL_chart0_point_mem_p1Zero_iff (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (p : PrimeSpectrum (R n)) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base p) ∈ p1Zero ↔
      Polynomial.aeval (psiChart0Coord n T) h ∈ p.asIdeal := by
  rw [phiFixedL_chart0_point_eq n T h hh p, evalAt_apply_aeval]
  exact chartMorphism0_mem_p1Zero_iff _ p

/-- **Dictionary, `1`**: the first-chart point attached to `p` maps to `1` iff `h(u) - 1`
vanishes at `p`. -/
theorem phiFixedL_chart0_point_mem_p1One_iff (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (p : PrimeSpectrum (R n)) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base p) ∈ p1One ↔
      Polynomial.aeval (psiChart0Coord n T) h - 1 ∈ p.asIdeal := by
  rw [phiFixedL_chart0_point_eq n T h hh p, evalAt_apply_aeval]
  exact chartMorphism0_mem_p1One_iff _ p

/-- **Boundary dictionary**: a first-chart point of `Y_n` maps into `{0, 1, ∞}` exactly when
`h(u)` is `0` or `1` at `p`. -/
theorem phiFixedL_chart0_point_mem_boundary_iff (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (p : PrimeSpectrum (R n)) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base p) ∈ boundarySetGlued ↔
      (Polynomial.aeval (psiChart0Coord n T) h ∈ p.asIdeal ∨
        Polynomial.aeval (psiChart0Coord n T) h - 1 ∈ p.asIdeal) := by
  rw [phiFixedL_chart0_point_eq n T h hh p, evalAt_apply_aeval]
  exact chartMorphism0_mem_boundarySetGlued_iff _ p

/-- **Avoidance dictionary**: a first-chart point of `Y_n` avoids `{0, 1, ∞}` exactly when
both `h(u)` and `h(u) - 1` are nonzero at `p`.  This is the ring-level form of the
`AvoidsBoundary` obligations of the B1/B2 lanes. -/
theorem phiFixedL_chart0_point_notMem_boundary_iff (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (p : PrimeSpectrum (R n)) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base p) ∉ boundarySetGlued ↔
      (Polynomial.aeval (psiChart0Coord n T) h ∉ p.asIdeal ∧
        Polynomial.aeval (psiChart0Coord n T) h - 1 ∉ p.asIdeal) := by
  rw [phiFixedL_chart0_point_mem_boundary_iff, not_or]

/-! ## 4. The reduction used by the branch lane -/

/-- **Ramification + value ⇒ boundary (first chart).**  If every first-chart ramification point
`p` of `phiFixedL` satisfies the ring condition "`h(u)` or `h(u) - 1` vanishes at `p`", then
the image of the first-chart part of the ramification locus lies in `{0, 1, ∞}`.  This turns
the point-level obligation of a branch input into a ring condition on `R n`, i.e. into the
form in which the value-level data (`Mzk1G1PsiBranchSetActual` /
`Mzk1G1PsiM2AnalyticActual`) can be consumed. -/
theorem phiFixedL_chart0_ram_mem_boundary_of_value (n : Nat) (T : Finset ℚ)
    (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (phiFixedL n T h hh)]
    (hval : ∀ p : PrimeSpectrum (R n),
      (fermatChart0ToCurve n).base p ∈ Ram (phiFixedL n T h hh) →
        (Polynomial.aeval (psiChart0Coord n T) h ∈ p.asIdeal ∨
          Polynomial.aeval (psiChart0Coord n T) h - 1 ∈ p.asIdeal)) :
    ∀ p : PrimeSpectrum (R n), (fermatChart0ToCurve n).base p ∈ Ram (phiFixedL n T h hh) →
      phiFixedL n T h hh ((fermatChart0ToCurve n).base p) ∈ boundarySetGlued := by
  intro p hp
  rw [phiFixedL_chart0_point_mem_boundary_iff n T h hh p]
  exact hval p hp

/-! ## Axiom checks -/

#print axioms chartMorphism0_mem_boundarySetGlued_iff
#print axioms evalAt_apply_aeval
#print axioms phiFixedL_chart0_point_eq
#print axioms phiFixedL_chart0_point_mem_p1Zero_iff
#print axioms phiFixedL_chart0_point_mem_p1One_iff
#print axioms phiFixedL_chart0_point_mem_boundary_iff
#print axioms phiFixedL_chart0_point_notMem_boundary_iff
#print axioms phiFixedL_chart0_ram_mem_boundary_of_value

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChart0BoundaryActual
