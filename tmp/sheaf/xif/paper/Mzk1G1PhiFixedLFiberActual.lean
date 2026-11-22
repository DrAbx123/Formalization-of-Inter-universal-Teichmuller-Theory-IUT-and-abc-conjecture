/-
# B1 (owner emmy lane): structural fibre reduction for `phiFixedL = psiFixed ≫ hPolyL`

This is the phiFixedL counterpart of section 4 of `Mzk1G1PhiFiberFiniteFixedActual`
(which treats `phiFixed = psiFixed ≫ hPoly`).  The reduction itself does not use any chart
formula: it only uses the two-piece cover of `Y_n` and grace's fact that a point of the
second piece (`qPiece`) with `r ≠ 0` already lies in the image of the first chart
(`qPiece_mem_range_chart0`).  Therefore it transports verbatim to `phiFixedL`.

## What is proved here

1. `phiFixedL_fiber_subset`: the fibre of `phiFixedL` over any point `q` of `P^1` is covered
   by (the first-chart image of) the first-chart fibre together with the *fixed* finite
   `r = 0` locus of `qPiece`; all `q`-dependence sits in the first chart.
2. `phiFixedL_fiber_finite_of_chart0`: a finite bound on the first-chart part of the fibre
   makes the whole fibre finite (scoped `0 < n`, so that `finite_primes_chartR` applies).

The first-chart input is supplied by `Mzk1G1PhiFixedLChart0Actual`
(`phiFixedL_chart0_fibre_subset` / `phiFixedL_chart0_fiber_finite`); the assembly over the
lambda-chart points is in `Mzk1G1PhiFixedLLambdaPointActual`.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFiberFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1PsiCoverActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLFiberActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartFiniteGActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFiberFiniteActual
open scoped AlgebraicGeometry

/-! ## 1. The fibre is covered by the first chart and the `r = 0` locus -/

/-- **The fibre of `phiFixedL` is covered by the first chart and the `r = 0` locus.**
Identical reduction to the `phiFixed` case: the second piece of `Y_n` contributes only the
fixed, finite `r = 0` set, so the `q`-dependence of the fibre is entirely first-chart. -/
theorem phiFixedL_fiber_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (q : projectiveLineGlued) :
    (phiFixedL n T h hh).base ⁻¹' {q} ⊆
      (fermatChart0ToCurve n).base '' ((fermatChart0ToCurve n).base ⁻¹'
        ((phiFixedL n T h hh).base ⁻¹' {q}))
      ∪ (qPiece n T).base '' {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
          algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
            P.asIdeal} := by
  intro z hz
  rcases cover_point n T z with ⟨x, rfl⟩ | ⟨P, rfl⟩
  · exact Or.inl ⟨x, hz, rfl⟩
  · by_cases hP : algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
        P.asIdeal
    · exact Or.inr ⟨P, hP, rfl⟩
    · left
      have hP' : algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))
          (r1 n) ∉ P.asIdeal := by
        rwa [show r1 n = chartR n from rfl]
      obtain ⟨x, hx⟩ := qPiece_mem_range_chart0 n T P hP'
      refine ⟨x, ?_, hx⟩
      show (phiFixedL n T h hh).base ((fermatChart0ToCurve n).base x) = q
      rw [hx]
      exact hz

/-! ## 2. Scheme-level interface: first-chart input gives the whole fibre -/

/-- **Consumer interface for B1 (phiFixedL version)**: a finite bound on the *first-chart*
part of the fibre of `phiFixedL` over `q` makes the whole fibre finite.  The second chart
contributes only the fixed `r = 0` locus, finite by `finite_primes_chartR` (scoped: `0 < n`). -/
theorem phiFixedL_fiber_finite_of_chart0 (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (q : projectiveLineGlued) (S : Set (PrimeSpectrum (R n)))
    (hS : S.Finite)
    (hsub : (fermatChart0ToCurve n).base ⁻¹'
      ((phiFixedL n T h hh).base ⁻¹' {q}) ⊆ S) :
    ((phiFixedL n T h hh).base ⁻¹' {q}).Finite := by
  have hS1 : {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
      algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
        P.asIdeal}.Finite :=
    finite_primes_chartR n T hn
  have hU : (((fermatChart0ToCurve n).base '' S) ∪
      ((qPiece n T).base '' {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
        algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
          P.asIdeal})).Finite :=
    (hS.image (fermatChart0ToCurve n).base).union (hS1.image (qPiece n T).base)
  refine hU.subset ?_
  intro z hz
  rcases phiFixedL_fiber_subset n T h hh q hz with h1 | h1
  · obtain ⟨y, hy, rfl⟩ := h1
    exact Or.inl ⟨y, hsub hy, rfl⟩
  · exact Or.inr h1

/-! ## Axiom checks -/

#print axioms phiFixedL_fiber_subset
#print axioms phiFixedL_fiber_finite_of_chart0

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLFiberActual
