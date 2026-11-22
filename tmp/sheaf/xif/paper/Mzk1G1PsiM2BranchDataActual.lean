/- 
# B1-B (owner emmy lane): assembling the analytic M2 target with the Branch data

This file is a **pure interface adaptation**: it mechanically assembles

* henry's analytic B1 target `M2AnalyticTarget` (`Mzk1G1PsiM2AnalyticActual`, route §4.3
  L298-334) and
* the value-level branch sets of `psiFixed` (`Mzk1G1PsiBranchSetActual`),

into the three contracts that the B1/B3 lane consumes:

1. **the `hbranch` input of `Mzk1G1B1FinalActual.b1FiniteProducer_of_branch_and_avoid`**
   (`hbranch_data`, `hbranch_data_of_target`, `b1_hbranch_uniform`) plus the value form of
   the target's fourth conjunct (`h0_data`);
2. **the two branch inputs `hpsi`, `hb` of
   `Mzk1G1PhiFixedLBranchSupportActual.phiFixedL_branch_subset`**
   (`hpsi_data`, `hb_data`, and their assembly `branch_support_of_data`);
3. **andrew's `havoid` input**, i.e. `AvoidsBoundary n (phiFixedL n Tr h hh) T`
   (`phiFixedL_T_avoid_data`, `b1Witness_of_T_avoid`, `b1FiniteProducer_of_T_avoid`),
   carried out at the value level of the lambda chart (section c).

No new mathematics is introduced; every statement below is either an unpacking of an
existing definition or a reduction to the explicit parameters named in the docstrings.

## 1. `hbranch`: the finiteness half is immediate, the Belyi content comes from the target

`b1FiniteProducer_of_branch_and_avoid` consumes only `Tr.Nonempty` and `0 < h.natDegree`
from the branch data (the branch/critical-value content is recorded separately by
`phiFixedL_branch_subset`).  Hence `hbranch_data` can be discharged by the *minimal*
witness `Tr = T`, `h = X` (`Polynomial.X_ne_zero`, `0 < natDegree X`).  This is honest but
carries **no Belyi content**: `h = X` is not admissible for the B3 branch conditions (its
critical values are `{1} ∪ {∞}`, it does not send the branch set of `psiFixed` into
`{0,1}`).  The paper-relevant polynomial is the `q` of `M2AnalyticTarget`; the variant
`hbranch_data_of_target` extracts exactly that `q` from the target as an explicit input
(`Mzk1G1PsiM2ProducerActual.mzk1Lemma24Target_of_zero` gives the base case, the §4.3
recursion is kurt's/henry's).  There `h ≠ 0` is derived from `0 < q.natDegree`.

## 2. `hpsi`, `hb`: the branch/value dictionary is *not* in the tree -- explicit parameters

Both target shapes are statements about **points of `P^1`** (`BelyiRamification.Branch`),
whereas `M2AnalyticTarget` is a statement about **values**.  What exists in the tree is the
lambda-chart dictionary of the *first chart*, re-proved below
(`chartMorphism0_mem_boundarySetGlued_iff`, `phiFixedL_chart0_point_mem_boundary_iff`,
`phiFixedL_chart0_point_notMem_boundary_iff`); it is used for the avoidance statement (3).
It does **not** reach `Branch (psiFixed n T)` / `Branch (hPolyL h hh)`, because that needs
(i) the second (`t`-)chart dictionary and (ii) a scheme-level "branch locus = critical
values" bridge, neither of which is available.  Therefore `hpsi_data` / `hb_data` are
**shape-matching transcriptions** with the missing dictionary carried as the explicit
structure `P1ValueDictionary`:

* `val : projectiveLineGlued → Option ℂ` reads off the `λ`-coordinate of a point of the
  glued `P^1` (`none` is the point `∞`);
* `val_boundary` : `{0, 1, ∞}` is exactly `val ∈ {some 0, some 1, none}`;
* `val_p1Zero` : a point of `p1Zero` has value `some 0`;
* `val_hPolyL` : `hPolyL h hh` acts on values by `h` (`λ ↦ h(λ)`), cf.
  `Mzk1G1PsiHPolyLambdaActual.hPolyL_lambda_chart`.

It is deliberately **not** downgraded to a `Set ℂ` statement: the conclusions are the
scheme-level `Branch ⊆ boundarySetGlued`.

## 3. `havoid`: this one is fully proved

`phiFixedL_T_avoid_data` proves `AvoidsBoundary n (phiFixedL n Tr h hh) T` from

* `T ⊆ DTFixed n Tr` (the protected-set choice, route B2; `DTFixed` is the first-chart
  protected set of `Mzk1G1B2FixedActual`, and
  `Mzk1G1B2FixedActual.psiFixed_preimage_p1Zero_eq_DT` identifies it with
  `psiFixed n Tr ⁻¹' p1Zero`), and
* `h(0) ∉ {0,1}` -- taken in the exact form of the fourth conjunct of `M2AnalyticTarget`.

The proof is the value computation at the protected points: on the first chart `phiFixedL`
is the lambda-chart point of coordinate `h(u)` (`phiFixedL_chart0_point`, from
`Mzk1G1PsiHPolyLambdaFactsActual.phiFixedL_chart0`), at a protected point `u = 0` we have
`h(u) ≡ h(0) mod p` (`Mzk1G1PsiPhiDTActual.phiFixedL_chart0_value_sub_at_DT`, the value
layer of the `D_T` computation), and for a *prime* ideal `algebraMap ℚ ↪ R` hits `p` only at
`0` (`algebraMap_rat_mem_prime_iff`).  Hence `h(u) ∈ p ↔ h(0) = 0` and
`h(u) - 1 ∈ p ↔ h(0) = 1`, so the boundary dictionary gives avoidance.  No explicit
parameter is left except `T ⊆ D_T` itself.

## Provenance note on the lambda-chart dictionary

`Mzk1G1PhiFixedLChart0BoundaryActual` (peer file, 2026-11-17 08:23) states the same
dictionary, but it does not build: its `phiFixedL_chart0_point_eq` step must identify
`evalAt (psiChart0Coord n T) h` with `Polynomial.aeval (psiChart0Coord n T) h`, and the
`simpa` there fails, so its downstream lemmas carry `sorryAx` (watchdog log 08:28:43).  Any
file importing it fails with it.  The re-proof below avoids that step entirely by using
`Mzk1G1PsiHPolyLambdaFactsActual.phiFixedL_chart0`, which is already stated with `aeval`.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticActual
import tmp.sheaf.xif.paper.Mzk1G1PsiBranchSetActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLBranchSupportActual
import tmp.sheaf.xif.paper.Mzk1G1B1FinalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaFactsActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1ZeroJudgeActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1OneJudgeActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLInfinityActual
import tmp.sheaf.xif.paper.Mzk1G1PsiPhiDTActual
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed5Actual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 800000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2BranchDataActual

open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiBranchSetActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaFactsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1OneJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLInfinityActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLBranchSupportActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1FinalActual

/-! ## a) The `hbranch` data of `B1FiniteProducer` -/

/-- **Minimal `hbranch` data.**  For every nonempty finite set `T` of rational parameters
there is a nonempty `Tr` and a nonzero polynomial `h` of positive degree: take `Tr = T` and
`h = X`.  Only `Tr.Nonempty` and `0 < h.natDegree` are consumed by the finiteness half of
B1 (`Mzk1G1B1FinalActual.b1FiniteProducer_of_branch_and_avoid`); this witness carries no
Belyi content (see the file header, and `hbranch_data_of_target` for the paper's `q`). -/
theorem hbranch_data (n : Nat) (T : Finset ℚ) (hT : T.Nonempty) :
    ∃ (Tr : Finset ℚ), Tr.Nonempty ∧ ∃ (h : Polynomial ℚ) (hh : h ≠ 0), 0 < h.natDegree :=
  ⟨T, hT, Polynomial.X, Polynomial.X_ne_zero, by rw [Polynomial.natDegree_X]; norm_num⟩

/-- **`hbranch` data from the analytic target** (route §4.3): the polynomial `q` of
`M2AnalyticTarget` is nonzero and of positive degree, so it is a legitimate `h`; the
protected set is the given `T`.  This is the paper-relevant half of `hbranch`: the Belyi
content of `q` (branch values and critical values in `{0,1}`, `q(0) ∉ {0,1}`) is recorded in
`hpsi_data` / `hb_data` below; the existence of `q` is henry's/kurt's `M2AnalyticTarget`. -/
theorem hbranch_data_of_target (T : Finset ℚ) (hT : T.Nonempty) {Branch : Finset ℂ}
    (hM2 : M2AnalyticTarget Branch) :
    ∃ (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0), Tr.Nonempty ∧ 0 < h.natDegree := by
  obtain ⟨q, hdeg, -, -, -⟩ := hM2
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hdeg
  exact ⟨T, q, hq, hT, hdeg⟩

/-- **The value form of the target's fourth conjunct**: some nonconstant rational polynomial
`q` (the target's `q`) does not take the values `0` or `1` at `0`.  This is
`M2AnalyticTarget`'s `q(0) ∉ {0,1}` transported from `ℂ` to `ℚ` by `aeval_zero_eq`, i.e. the
`h(0) ∉ {0,1}` hypothesis of `phiFixedL_T_avoid_data`. -/
theorem h0_data {Branch : Finset ℂ} (hM2 : M2AnalyticTarget Branch) :
    ∃ q : Polynomial ℚ, Polynomial.eval (0 : ℚ) q ∉ ({0, 1} : Set ℚ) := by
  obtain ⟨q, _hdeg, _hbranch, _hcrit, h0⟩ := hM2
  refine ⟨q, ?_⟩
  intro hmem
  apply h0
  rw [aeval_zero_eq]
  rcases (show Polynomial.eval (0 : ℚ) q = 0 ∨ Polynomial.eval (0 : ℚ) q = 1 by
    simpa using hmem) with h | h
  · simp [h]
  · simp [h]

/-- **The `hbranch` input in the exact shape required by
`b1FiniteProducer_of_branch_and_avoid`**: uniformly over the finite point sets `T` of
`Y_n = fermatCurveScheme n`.  This closes the first of the two explicit inputs of `B1` (the
second is andrew's T-avoidance, reduced to `T ⊆ D_T` and `h(0) ∉ {0,1}` by
`phiFixedL_T_avoid_data`). -/
theorem b1_hbranch_uniform (n : Nat) :
    ∀ T : Finset (fermatCurveScheme n),
      ∃ (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0), Tr.Nonempty ∧ 0 < h.natDegree :=
  fun _ => ⟨({0} : Finset ℚ), Polynomial.X, Polynomial.X_ne_zero, ⟨0, by simp⟩,
    by rw [Polynomial.natDegree_X]; norm_num⟩

/-! ## b) The branch inputs `hpsi` and `hb` of `phiFixedL_branch_subset` -/

/-- **Pending value dictionary of the glued `P^1`** (the open last mile): a reading of the
`λ`-coordinate of a point of `P^1` as an `Option ℂ` (`none` = the point `∞`), compatible with
the Belyi boundary and with the action of `hPolyL`.

Provenance: the *first chart* half is unconditional and is re-proved in this file (section
c, `chartMorphism0_mem_boundarySetGlued_iff` / `phiFixedL_chart0_point_mem_boundary_iff`).
What is missing in the tree is (i) the second (`t`-)chart dictionary and (ii) the
identification of the scheme-theoretic branch locus `Branch` with the analytic critical
values, which is exactly what `hpsi_data` / `hb_data` consume.

This structure carries data only (no new mathematics), so it is axiom-free by construction;
`#print axioms` is not applicable (it is a structure, not a theorem). -/
structure P1ValueDictionary where
  /-- Value (`λ`-coordinate) of a point of the glued `P^1`; `none` is `∞`. -/
  val : projectiveLineGlued → Option ℂ
  /-- The Belyi boundary is read off by `val`. -/
  val_boundary : ∀ y : projectiveLineGlued,
    y ∈ boundarySetGlued ↔ (val y = some 0 ∨ val y = some 1 ∨ val y = none)
  /-- Points of the `λ = 0` locus have value `0`. -/
  val_p1Zero : ∀ y : projectiveLineGlued, y ∈ p1Zero → val y = some 0
  /-- `hPolyL h hh` acts on values by `h` (`λ ↦ h(λ)`); this is the value form of
  `Mzk1G1PsiHPolyLambdaActual.hPolyL_lambda_chart`. -/
  val_hPolyL : ∀ (h : Polynomial ℚ) (hh : h ≠ 0) (y : projectiveLineGlued) (c : ℂ),
    val y = some c → val (hPolyL h hh y) = some (Polynomial.aeval c h)

/-- **`hpsi`: the first branch input of `phiFixedL_branch_subset`, shape-matched.**
Every branch point of `psiFixed n T` has a finite value lying in henry's finite branch set
`branchFixedFinite T` (`Mzk1G1PsiBranchSetActual`, the inversion image of the nonzero
critical values of `u = ∏ (X - t)`), and the first conjunct of `M2AnalyticTarget` at `q = h`
sends those values into `{0,1}`; hence `hPolyL h hh` carries `Branch (psiFixed n T)` into the
Belyi boundary.

The two point/value bridges are explicit: `hval_branch` (value of a `psiFixed`-branch point)
and `D.val_hPolyL` (value of the image).  See the file header for why no unconditional
scheme-level dictionary exists yet. -/
theorem hpsi_data (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (psiFixed n T)]
    (D : P1ValueDictionary)
    (hval_branch : ∀ y ∈ (Branch (psiFixed n T) : Set projectiveLineGlued),
      ∃ c ∈ branchFixedFinite T, D.val y = some c)
    (hbranch_henry : ∀ c ∈ branchFixedFinite T, Polynomial.aeval c h ∈ ({0, 1} : Set ℂ)) :
    hPolyL h hh '' (Branch (psiFixed n T) : Set projectiveLineGlued) ⊆ boundarySetGlued := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨c, hc, hv⟩ := hval_branch x hx
  have hv' : D.val (hPolyL h hh x) = some (Polynomial.aeval c h) := D.val_hPolyL h hh x c hv
  rw [D.val_boundary]
  rcases (show Polynomial.aeval c h = 0 ∨ Polynomial.aeval c h = 1 by
    simpa using hbranch_henry c hc) with hc0 | hc1
  · exact Or.inl (by rw [hv', hc0])
  · exact Or.inr (Or.inl (by rw [hv', hc1]))

/-- **`hpsi` from the analytic target.**  The target `M2AnalyticTarget Branch` is an
existential in `q`; this variant extracts its `q` (nonzero since `0 < q.natDegree`) and
concludes the `hpsi` shape for that `q`.  The remaining inputs are exactly the dictionary
hypotheses of `hpsi_data`. -/
theorem hpsi_data_of_m2 (n : Nat) (T : Finset ℚ) [LocallyOfFinitePresentation (psiFixed n T)]
    (D : P1ValueDictionary)
    (hval_branch : ∀ y ∈ (Branch (psiFixed n T) : Set projectiveLineGlued),
      ∃ c ∈ branchFixedFinite T, D.val y = some c)
    (hM2 : M2AnalyticTarget (branchFixedFinite T)) :
    ∃ (h : Polynomial ℚ) (hh : h ≠ 0),
      hPolyL h hh '' (Branch (psiFixed n T) : Set projectiveLineGlued) ⊆ boundarySetGlued := by
  obtain ⟨q, hdeg, hbr, -, -⟩ := hM2
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hdeg
  exact ⟨q, hq, hpsi_data n T q hq D hval_branch hbr⟩

/-- **`hb`: the second branch input of `phiFixedL_branch_subset`, shape-matched.**
Every point of `Branch (hPolyL h hh)` is either `∞` (value `none`) or has a finite value
`z = h(w)` at a **critical point** `w` of `h`; the third conjunct of `M2AnalyticTarget` at
`q = h` says critical values of `h` lie in `{0,1}`, so the whole branch locus lies in the
Belyi boundary.

The dictionary hypothesis `hbranch_pts` is the point/value form of "the branch locus of
`hPolyL h hh` is the set of critical values of `h` (plus `∞`, which is automatically a branch
value for a nonconstant polynomial)"; it is the remaining scheme-level bridge (file header). -/
theorem hb_data (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPolyL h hh)]
    (D : P1ValueDictionary)
    (hcrit : ∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative h) = 0 →
      Polynomial.aeval z h ∈ ({0, 1} : Set ℂ))
    (hbranch_pts : ∀ y ∈ (Branch (hPolyL h hh) : Set projectiveLineGlued),
      D.val y = none ∨ ∃ (w z : ℂ), D.val y = some z ∧
        Polynomial.aeval w (Polynomial.derivative h) = 0 ∧ Polynomial.aeval w h = z) :
    Branch (hPolyL h hh) ⊆ boundarySetGlued := by
  intro y hy
  rcases hbranch_pts y hy with hv | ⟨w, z, hv, hw, hwz⟩
  · rw [D.val_boundary]
    exact Or.inr (Or.inr hv)
  · rcases (show Polynomial.aeval w h = 0 ∨ Polynomial.aeval w h = 1 by
      simpa using hcrit w hw) with hc0 | hc1
    · rw [D.val_boundary]
      exact Or.inl (by rw [hv, ← hwz, hc0])
    · rw [D.val_boundary]
      exact Or.inr (Or.inl (by rw [hv, ← hwz, hc1]))

/-- **The branch-support contract of `phiFixedL` with `hpsi`/`hb` filled in.**
This is `Mzk1G1PhiFixedLBranchSupportActual.phiFixedL_branch_subset` with its two explicit
branch inputs supplied by `hpsi_data` and `hb_data`; the only inputs are the value
dictionary and henry's analytic target conjuncts. -/
theorem branch_support_of_data (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (psiFixed n T)]
    [LocallyOfFinitePresentation (hPolyL h hh)]
    [LocallyOfFinitePresentation (phiFixedL n T h hh)]
    (D : P1ValueDictionary)
    (hval_branch : ∀ y ∈ (Branch (psiFixed n T) : Set projectiveLineGlued),
      ∃ c ∈ branchFixedFinite T, D.val y = some c)
    (hbranch_henry : ∀ c ∈ branchFixedFinite T, Polynomial.aeval c h ∈ ({0, 1} : Set ℂ))
    (hcrit : ∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative h) = 0 →
      Polynomial.aeval z h ∈ ({0, 1} : Set ℂ))
    (hbranch_pts : ∀ y ∈ (Branch (hPolyL h hh) : Set projectiveLineGlued),
      D.val y = none ∨ ∃ (w z : ℂ), D.val y = some z ∧
        Polynomial.aeval w (Polynomial.derivative h) = 0 ∧ Polynomial.aeval w h = z) :
    Branch (phiFixedL n T h hh) ⊆ boundarySetGlued :=
  phiFixedL_branch_subset n T h hh
    (hpsi_data n T h hh D hval_branch hbranch_henry)
    (hb_data h hh D hcrit hbranch_pts)

/-! ## c) The lambda-chart value dictionary of `phiFixedL` (first chart) -/

/-- **Lambda-chart boundary dictionary** (general base ring): a lambda-chart point with value
`a` lies on the Belyi boundary `{0, 1, ∞}` exactly when `a` or `a - 1` vanishes at `p`.  The
infinite slot cannot occur in the lambda chart (`chartMorphism0_not_mem_p1Infinity`); the two
finite slots are the judge lemmas `chartMorphism0_mem_p1Zero_iff` /
`chartMorphism0_mem_p1One_iff`.

This is the value dictionary announced (and blocked) in `Mzk1G1PhiFixedLChart0BoundaryActual`;
it is re-proved here because that file does not build (see the file header). -/
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

/-- **Point form of the first chart of `phiFixedL`**: on the first chart of `Y_n`, `phiFixedL`
is the lambda-chart point of coordinate `h(u)`, `u = psiChart0Coord n T` (from
`Mzk1G1PsiHPolyLambdaFactsActual.phiFixedL_chart0`, stated with `Polynomial.aeval`; the
`evalAt`-form `Mzk1G1PhiFixedLChart0Actual.phiFixedL_chart0_eq` is not used, which is exactly
the step where `Mzk1G1PhiFixedLChart0BoundaryActual` breaks). -/
theorem phiFixedL_chart0_point (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (p : PrimeSpectrum (R n)) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base p) =
      chartMorphism0 (Polynomial.aeval (psiChart0Coord n T) h) p := by
  have hm : fermatChart0ToCurve n ≫ phiFixedL n T h hh =
      chartMorphism0 (Polynomial.aeval (psiChart0Coord n T) h) := by
    rw [← psiOpenCover_f_false n T]
    exact phiFixedL_chart0 n T h hh
  have hx := congrArg (fun g : fermatChart0Scheme n ⟶ projectiveLineGlued => g.base p) hm
  simpa using hx

/-- **Boundary dictionary of the first chart**: a first-chart point of `Y_n` maps into
`{0,1,∞}` exactly when `h(u)` is `0` or `1` at `p` (`u = psiChart0Coord n T`). -/
theorem phiFixedL_chart0_point_mem_boundary_iff (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (p : PrimeSpectrum (R n)) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base p) ∈ boundarySetGlued ↔
      (Polynomial.aeval (psiChart0Coord n T) h ∈ p.asIdeal ∨
        Polynomial.aeval (psiChart0Coord n T) h - 1 ∈ p.asIdeal) := by
  rw [phiFixedL_chart0_point n T h hh p]
  exact chartMorphism0_mem_boundarySetGlued_iff _ p

/-- **Avoidance dictionary**: a first-chart point of `Y_n` avoids `{0,1,∞}` exactly when both
`h(u)` and `h(u) - 1` are nonzero at `p`.  This is the ring-level form of the `AvoidsBoundary`
obligation of the B1/B2 lanes. -/
theorem phiFixedL_chart0_point_notMem_boundary_iff (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (p : PrimeSpectrum (R n)) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base p) ∉ boundarySetGlued ↔
      (Polynomial.aeval (psiChart0Coord n T) h ∉ p.asIdeal ∧
        Polynomial.aeval (psiChart0Coord n T) h - 1 ∉ p.asIdeal) := by
  rw [phiFixedL_chart0_point_mem_boundary_iff, not_or]

/-! ## d) The `havoid` input: `T ⊆ D_T` and `h(0) ∉ {0,1}` imply avoidance -/

/-- **Rational scalars in a prime ideal.**  For a `ℚ`-algebra `R` and a prime ideal `p`, the
image of `q : ℚ` lies in `p` iff `q = 0` (any nonzero rational is a unit, and a prime ideal
cannot contain a unit). -/
theorem algebraMap_rat_mem_prime_iff {R : Type} [CommRing R] [Algebra ℚ R]
    (p : Ideal R) (hp : p.IsPrime) (q : ℚ) :
    algebraMap ℚ R q ∈ p ↔ q = 0 := by
  constructor
  · intro hmem
    by_contra hq
    have hmul : algebraMap ℚ R q * algebraMap ℚ R q⁻¹ ∈ p :=
      Ideal.mul_mem_right (algebraMap ℚ R q⁻¹) p hmem
    have hone : algebraMap ℚ R q * algebraMap ℚ R q⁻¹ = (1 : R) := by
      rw [← map_mul, mul_inv_cancel₀ hq, map_one]
    rw [hone] at hmul
    have htop : p = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      exact hmul
    exact hp.ne_top htop
  · rintro rfl
    simpa using p.zero_mem

/-- **Value at a protected point is the constant term.**  If `a - algebraMap ℚ R q` lies in a
prime ideal `p`, then `a ∈ p` iff `q = 0`.  This is the ring-level form of "the value of
`h(u)` at a point where `u = 0` is `h(0)`"
(`Mzk1G1PsiPhiDTActual.phiFixedL_chart0_value_sub_at_DT`). -/
theorem mem_iff_rat_eq_zero_of_sub_algebraMap_mem {R : Type} [CommRing R] [Algebra ℚ R]
    (p : Ideal R) (hp : p.IsPrime) {a : R} {q : ℚ}
    (h : a - algebraMap ℚ R q ∈ p) : a ∈ p ↔ q = 0 := by
  have hiff : algebraMap ℚ R q ∈ p ↔ q = 0 := algebraMap_rat_mem_prime_iff p hp q
  constructor
  · intro ha
    rw [← hiff]
    have hsum : algebraMap ℚ R q + (a - algebraMap ℚ R q) ∈ p := by
      rw [show algebraMap ℚ R q + (a - algebraMap ℚ R q) = a from by ring]
      exact ha
    exact (Ideal.add_mem_iff_left p h).mp hsum
  · intro hq
    have hb : algebraMap ℚ R q ∈ p := hiff.mpr hq
    have hsum : a = algebraMap ℚ R q + (a - algebraMap ℚ R q) := by ring
    rw [hsum]
    exact Ideal.add_mem p hb h

/-- **The `havoid` input of B1 (andrew's T-avoidance), reduced to `T ⊆ D_T` and
`h(0) ∉ {0,1}`.**  This is the shape of `b1FiniteProducer_of_branch_and_avoid`'s second input.

Proof: for `x ∈ T ⊆ DTFixed n Tr`, `x` is a first-chart point `(fermatChart0ToCurve n).base p`
with `u = psiChart0Coord n Tr ∈ p` (`psiChart0Coord_mem_iff`).  There `phiFixedL` is the
lambda-chart point of coordinate `h(u)` (`phiFixedL_chart0_point`), and the boundary
dictionary says `phiFixedL ... ∉ {0,1,∞}` iff `h(u) ∉ p` and `h(u) - 1 ∉ p`
(`phiFixedL_chart0_point_notMem_boundary_iff`).  Since `h(u) ≡ h(0) mod p`
(`phiFixedL_chart0_value_sub_at_DT`), those two conditions are `h(0) ≠ 0` and `h(0) ≠ 1`,
which is exactly the fourth conjunct of `M2AnalyticTarget` (`aeval_zero_eq`).

`T ⊆ DTFixed n Tr` is the only remaining input: it is the route-B2 choice of the protected
set (`Mzk1G1B2FixedActual.psiFixed_preimage_p1Zero_eq_DT` identifies `DTFixed` with
`psiFixed n Tr ⁻¹' p1Zero`, but the proof below only needs the defining chart-`0` shape). -/
theorem phiFixedL_T_avoid_data (n : Nat) (T : Finset (fermatCurveScheme n)) (Tr : Finset ℚ)
    (h : Polynomial ℚ) (hh : h ≠ 0) (hT : (T : Set (fermatCurveScheme n)) ⊆ DTFixed n Tr)
    (h0 : Polynomial.aeval (0 : ℂ) h ∉ ({0, 1} : Set ℂ)) :
    AvoidsBoundary n (phiFixedL n Tr h hh) T := by
  intro x hx
  have hxDT : x ∈ DTFixed n Tr := hT (by simpa using hx)
  simp only [DTFixed, Set.mem_image] at hxDT
  obtain ⟨p, hp, hpx⟩ := hxDT
  subst hpx
  haveI : p.asIdeal.IsPrime := p.isPrime
  have hu : psiChart0Coord n Tr ∈ p.asIdeal := (psiChart0Coord_mem_iff n Tr p.asIdeal).mpr hp
  change (phiFixedL n Tr h hh) ((fermatChart0ToCurve n).base p) ∉ boundarySetGlued
  rw [phiFixedL_chart0_point_notMem_boundary_iff n Tr h hh p]
  have hsub : Polynomial.aeval (psiChart0Coord n Tr) h -
      algebraMap ℚ (R n) (Polynomial.eval 0 h) ∈ p.asIdeal :=
    phiFixedL_chart0_value_sub_at_DT p.asIdeal hu h
  constructor
  · intro hmem
    have hq : Polynomial.eval 0 h = 0 :=
      (mem_iff_rat_eq_zero_of_sub_algebraMap_mem p.asIdeal p.isPrime hsub).mp hmem
    exact h0 (by simp [aeval_zero_eq, hq])
  · intro hmem
    have hsub1 : Polynomial.aeval (psiChart0Coord n Tr) h - 1 -
        algebraMap ℚ (R n) (Polynomial.eval 0 h - 1) ∈ p.asIdeal := by
      have heq : Polynomial.aeval (psiChart0Coord n Tr) h - 1 -
          algebraMap ℚ (R n) (Polynomial.eval 0 h - 1) =
          Polynomial.aeval (psiChart0Coord n Tr) h -
            algebraMap ℚ (R n) (Polynomial.eval 0 h) := by
        rw [map_sub, map_one]
        ring
      rw [heq]
      exact hsub
    have hq : Polynomial.eval 0 h - 1 = 0 :=
      (mem_iff_rat_eq_zero_of_sub_algebraMap_mem p.asIdeal p.isPrime hsub1).mp hmem
    have hq1 : Polynomial.eval 0 h = 1 := sub_eq_zero.mp hq
    exact h0 (by simp [aeval_zero_eq, hq1])

/-- **B1 witness for a single `T`, with `havoid` discharged.**  Combining
`phiFixedL_T_avoid_data` with the finiteness theorem
(`Mzk1G1PhiFixedLBoundaryActual.phiFixedL_boundaryPreimage_finite`, via
`b1Witness_of_branch_and_avoid`) gives the B1 witness morphism `phiFixedL n Tr h hh` with
finite boundary preimage, avoiding `{0,1,∞}` on `T`. -/
theorem b1Witness_of_T_avoid (n : Nat) (hn : 0 < n) (T : Finset (fermatCurveScheme n))
    (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) (hTr : Tr.Nonempty)
    (hdeg : 0 < h.natDegree)
    (hT : (T : Set (fermatCurveScheme n)) ⊆ DTFixed n Tr) (h0 : Polynomial.aeval (0 : ℂ) h ∉ ({0, 1} : Set ℂ)) :
    ∃ φ : fermatCurveScheme n ⟶ projectiveLineGlued,
      (φ.base ⁻¹' boundarySetGlued).Finite ∧ (∀ x ∈ T, φ.base x ∉ boundarySetGlued) :=
  b1Witness_of_branch_and_avoid n hn T Tr h hh hTr hdeg
    (phiFixedL_T_avoid_data n T Tr h hh hT h0)

/-- **The B1 producer with the `hbranch` half discharged and `havoid` reduced.**  The single
remaining input is andrew's avoidance data in the reduced form of `phiFixedL_T_avoid_data`
(`T ⊆ D_T`, `h(0) ∉ {0,1}` for each `T`). -/
theorem b1FiniteProducer_of_T_avoid (n : Nat) (hn : 0 < n)
    (havoid : ∀ (T : Finset (fermatCurveScheme n)) (Tr : Finset ℚ) (h : Polynomial ℚ)
      (hh : h ≠ 0), AvoidsBoundary n (phiFixedL n Tr h hh) T) :
    B1FiniteProducer n :=
  b1FiniteProducer_of_branch_and_avoid n hn (b1_hbranch_uniform n) havoid

/-! ## Axiom checks -/

#print axioms hbranch_data
#print axioms hbranch_data_of_target
#print axioms h0_data
#print axioms b1_hbranch_uniform
#print axioms hpsi_data
#print axioms hpsi_data_of_m2
#print axioms hb_data
#print axioms branch_support_of_data
#print axioms chartMorphism0_mem_boundarySetGlued_iff
#print axioms phiFixedL_chart0_point
#print axioms phiFixedL_chart0_point_mem_boundary_iff
#print axioms phiFixedL_chart0_point_notMem_boundary_iff
#print axioms algebraMap_rat_mem_prime_iff
#print axioms mem_iff_rat_eq_zero_of_sub_algebraMap_mem
#print axioms phiFixedL_T_avoid_data
#print axioms b1Witness_of_T_avoid
#print axioms b1FiniteProducer_of_T_avoid

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2BranchDataActual

