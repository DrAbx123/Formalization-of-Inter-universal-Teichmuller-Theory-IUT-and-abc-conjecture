/-
# B1 (owner emmy lane): the lambda-chart points of `P^1` in the phiFixedL fibre

This file assembles the first-chart fibre bound (`Mzk1G1PhiFixedLChart0Actual`) with the
structural reduction (`Mzk1G1PhiFixedLFiberActual`) into the scheme-level statement

  `phiFixedL.base ⁻¹' {lambda-chart point of rational coordinate c}`  is finite,

i.e. the phiFixedL counterpart of grace's `phi_fiber_finite_of_chartInf`.  Because `phiFixedL`
acts on the lambda chart by `lambda ↦ h(lambda)` (`hPolyL_lambda_chart`), the first-chart
condition is the single polynomial `h - C c`, so the proof is a direct
`finite_primes_of_gHom_poly` instance plus the fixed `r = 0` locus of the second chart.

Corollaries: the fibres over `p1Zero` (`lambda = 0`) and over `p1One` (`lambda = 1`), which
with the phiFixedL chart swap are *lambda*-chart points (no chart-transition needed, unlike
the old `phiFixed` where `lambda = 0` lay outside the t-chart).

Not covered here: `p1Infinity` (`t = 0`, i.e. `lambda = infinity`), whose first-chart
description goes through the t-chart piece of `hPolyL` (`localChartInf ≫ hPolyL`,
localized at `hRev`); that is the remaining B1 boundary input.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChart0Actual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLFiberActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLLambdaPointActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
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

/-! ## 1. Fibre over a lambda-chart closed point of rational coordinate -/

/-- **Scheme-level fibre finiteness at the lambda-chart points of rational coordinate.**
`y` is a point of the lambda chart `Spec Q[lambda]` containing `X - C c`; the fibre of
`phiFixedL` over its image is finite (nonconstant `h`, `T ≠ ∅`, `0 < n`). -/
theorem phiFixedL_fiber_finite_of_lambda (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (hT : T.Nonempty) (hdeg : 0 < h.natDegree) (c : ℚ)
    (y : PrimeSpectrum (Polynomial ℚ)) (hy : Polynomial.X - Polynomial.C c ∈ y.asIdeal) :
    ((phiFixedL n T h hh).base ⁻¹' {localChart0.base y}).Finite := by
  classical
  have hS0 : {x : fermatChart0Scheme n | gHom n T (h - Polynomial.C c) ∈ x.asIdeal}.Finite :=
    finite_primes_of_gHom_poly n T hT (h - Polynomial.C c) (sub_C_ne_zero hdeg c)
  have hpre0 : (fermatChart0ToCurve n).base ⁻¹'
      ((phiFixedL n T h hh).base ⁻¹' {localChart0.base y})
      ⊆ {x : fermatChart0Scheme n | gHom n T (h - Polynomial.C c) ∈ x.asIdeal} :=
    Mzk1G1PhiFixedLChart0Actual.phiFixedL_chart0_fibre_subset n T h hh c y hy
  have hS1 : {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
      algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
        P.asIdeal}.Finite :=
    finite_primes_chartR n T hn
  have hU : (((fermatChart0ToCurve n).base '' {x : fermatChart0Scheme n |
        gHom n T (h - Polynomial.C c) ∈ x.asIdeal})
      ∪ ((qPiece n T).base '' {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
          algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
            P.asIdeal})).Finite :=
    (hS0.image (fermatChart0ToCurve n).base).union (hS1.image (qPiece n T).base)
  refine hU.subset ?_
  intro z hz
  rcases Mzk1G1PhiFixedLFiberActual.phiFixedL_fiber_subset n T h hh
    (localChart0.base y) hz with h1 | h1
  · exact Or.inl (Set.image_mono hpre0 h1)
  · exact Or.inr h1

/-! ## 2. The boundary points `lambda = 0` and `lambda = 1` -/

/-- **The fibre of `phiFixedL` over `lambda = 0` is finite.** -/
theorem phiFixedL_fiber_finite_p1Zero (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (hT : T.Nonempty) (hdeg : 0 < h.natDegree) :
    ((phiFixedL n T h hh).base ⁻¹' p1Zero).Finite := by
  have hsub : p1Zero ⊆ {localChart0.base (chartPrime 0)} := by
    intro z hz
    rw [p1Zero] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    simp only [chartPoint, Set.mem_setOf_eq] at hp
    rw [chartPrime_eq_of_mem 0 p hp]
    exact Set.mem_singleton _
  exact (phiFixedL_fiber_finite_of_lambda n T h hh hn hT hdeg 0 (chartPrime 0)
    (chartPrime_mem 0)).subset (Set.preimage_mono hsub)

/-- **The fibre of `phiFixedL` over `lambda = 1` is finite.** -/
theorem phiFixedL_fiber_finite_p1One (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (hT : T.Nonempty) (hdeg : 0 < h.natDegree) :
    ((phiFixedL n T h hh).base ⁻¹' p1One).Finite := by
  have hsub : p1One ⊆ {localChart0.base (chartPrime 1)} := by
    intro z hz
    rw [p1One] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    simp only [chartPoint, Set.mem_setOf_eq] at hp
    rw [chartPrime_eq_of_mem 1 p hp]
    exact Set.mem_singleton _
  exact (phiFixedL_fiber_finite_of_lambda n T h hh hn hT hdeg 1 (chartPrime 1)
    (chartPrime_mem 1)).subset (Set.preimage_mono hsub)

/-! ## Axiom checks -/

#print axioms phiFixedL_fiber_finite_of_lambda
#print axioms phiFixedL_fiber_finite_p1Zero
#print axioms phiFixedL_fiber_finite_p1One

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLLambdaPointActual
