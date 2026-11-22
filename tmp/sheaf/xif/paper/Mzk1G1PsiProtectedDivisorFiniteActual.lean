/-
# B1 part A: the protected-divisor quotient `R n ⧸ (chartX - t)` is finite over ℚ

Consumer: `Mzk1G1PhiFiberFiniteFixedActual` (B1, emmy lane), handoff item (a): the ring-level
input `Module.Finite ℚ (R n ⧸ Ideal.span {chartX n - algebraMap ℚ (R n) t})` for `t ∈ T`,
i.e. finiteness of the protected divisor D_T = {u ∈ p} over the λ = 0 point of P^1.

## Route (narrow, reusing the already-proved g-structure)

R n = ℚ[x,y]/(x^n + y^n - 1) with chartX = x, chartY = y, and
u = psiChart0Coord n T = ∏_{s ∈ T} (chartX - s) is the protected chart product, so that
`gAlgebra n T` is the ℚ[t]-algebra structure t ↦ u.  Mzk1G1PsiQuotientFiniteActual gives

  quot_finiteDim (T) (hT) (f) (hf) : Module.Finite ℚ (R n ⧸ (f(u))).

Take T = {t} and **f = X** (not X - C t!).  f is substituted at u, so with f = X one has
f(u) = u = chartX - t, which is exactly the linear relation wanted; with f = X - C t one
would get u - t = chartX - 2t instead.  Since `psiChart0Coord n {t} = chartX - algebraMap ℚ (R n) t`
(`Finset.prod_singleton`), the quotient ideal is exactly `(chartX - t)`.

All declarations depend only on [propext, Classical.choice, Quot.sound].
No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiQuotientFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartFiniteGActual
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiProtectedDivisorFiniteActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartFiniteGActual

/-- `psiChart0Coord` on the singleton `{t}` is the linear factor `chartX - t`. -/
theorem psiChart0Coord_singleton (n : Nat) (t : ℚ) :
    psiChart0Coord n ({t} : Finset ℚ) = chartX n - algebraMap ℚ (R n) t := by
  rw [psiChart0Coord, Finset.prod_singleton]

/-- **B1 part A.** For every `n` and every `t : ℚ`, the quotient of the Fermat chart ring
`R n = ℚ[x,y]/(x^n + y^n - 1)` by the linear relation `x = t` is finite-dimensional over ℚ.
(Modulo `x = t` the coordinate y satisfies the monic relation `y^n = 1 - t^n`.)

This is the ring-level finiteness of the protected divisor `D_T = {x = t, t ∈ T}` over the
λ = 0 point of P^1. -/
theorem protectedDivisor_quot_finite (n : Nat) (t : ℚ) :
    Module.Finite ℚ (R n ⧸ Ideal.span ({chartX n - algebraMap ℚ (R n) t} : Set (R n))) := by
  letI := gAlgebra n ({t} : Finset ℚ)
  have h := Mzk1G1PsiQuotientFiniteActual.quot_finiteDim n ({t} : Finset ℚ)
    (Finset.singleton_nonempty t)
    Polynomial.X Polynomial.X_ne_zero
  -- h : Module.Finite ℚ (R n ⧸ Ideal.span {algebraMap ℚ[X] (R n) X}), and
  -- algebraMap X = gHom X = psiChart0Coord n {t} = chartX - t.
  have hX : algebraMap (Polynomial ℚ) (R n) Polynomial.X
      = chartX n - algebraMap ℚ (R n) t := by
    rw [show algebraMap (Polynomial ℚ) (R n) = gHom n ({t} : Finset ℚ) from rfl,
      gHom_X n ({t} : Finset ℚ)]
    exact psiChart0Coord_singleton n t
  rw [hX] at h
  exact h

/-- The form in which the protected-divisor argument uses the statement: the hypothesis
`t ∈ T` is what the consumer has available. -/
theorem protectedDivisor_quot_finite_of_mem (n : Nat) (T : Finset ℚ) (t : ℚ) (_ht : t ∈ T) :
    Module.Finite ℚ (R n ⧸ Ideal.span ({chartX n - algebraMap ℚ (R n) t} : Set (R n))) :=
  protectedDivisor_quot_finite n t

#print axioms psiChart0Coord_singleton
#print axioms protectedDivisor_quot_finite
#print axioms protectedDivisor_quot_finite_of_mem

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiProtectedDivisorFiniteActual
