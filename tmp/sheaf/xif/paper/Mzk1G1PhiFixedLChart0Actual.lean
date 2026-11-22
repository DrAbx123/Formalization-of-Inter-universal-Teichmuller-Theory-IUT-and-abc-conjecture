/-
# B1 (owner emmy lane): the **first chart** of `phiFixedL = psiFixed ≫ hPolyL`

This is the phiFixedL counterpart of section 3 of `Mzk1G1PhiFiberFiniteFixedActual` (which
treats `phiFixed = psiFixed ≫ hPoly`).  The chart swap of `psiFixed` sends the first Fermat
chart to the **lambda** chart of P^1, and `hPolyL` acts on the lambda chart by
`lambda ↦ h(lambda)` (`hPolyL_lambda_chart` of `Mzk1G1PsiHPolyLambdaActual`).  Hence, unlike
the old `phiFixed` (whose first chart forced `t = h(1/u)` and needed the reversed polynomial
`hRev` and the `hPolyLam` pieces), the first chart of `phiFixedL` is the plain polynomial
condition

  `lambda' = h(u)`,  `u = psiChart0Coord n T`  (phiFixedL_chart0_eq),

so the fibre of `phiFixedL` over the lambda-chart closed point `lambda = c` is cut out on the
first chart by `h(u) - c` — a single `finite_primes_of_gHom_poly` instance.

## What is proved here

1. `phiFixedL_chart0_eq` / `phiFixedL_chart0_apply`: the first piece of `Y_n` maps by
   `lambda' = h(u)` (`chartMorphism0 (evalAt u h)`).
2. `phiFixedL_chart0_fibre_subset`: over a lambda-chart point `y` with `X - C c ∈ y`, the
   first-chart part of the fibre lies in the zero set of `h - C c` at `u`.
3. `phiFixedL_chart0_fiber_finite`: that first-chart part is finite (ring level,
   `finite_primes_of_gHom_poly`), for nonconstant `h`.

The structural reduction (second chart contributes only the fixed `r = 0` locus) and the
scheme-level assembly are in `Mzk1G1PhiFixedLFiberActual` / `Mzk1G1PhiFixedLLambdaPointActual`.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFiberFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartFiniteGActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFiberTemplateActual
import tmp.sheaf.xif.paper.Mzk1G1PsiPhiFixedLZeroFiberActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChart0Actual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
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

/-! ## 1. The first chart of phiFixedL: lambda' = h(u) -/

/-- **phiFixedL on the first chart of Y_n**: the coordinate is `lambda = u` and `hPolyL` acts
on the lambda chart by `hPolyL_lambda_chart`, so the target is the lambda-chart point of
coordinate `h(u)`.  (For the old `phiFixed` this chart instead produced `t = h(1/u)`.) -/
theorem phiFixedL_chart0_eq (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    fermatChart0ToCurve n ≫ phiFixedL n T h hh =
      chartMorphism0 (R := R n) (evalAt (R := R n) (psiChart0Coord n T) h) := by
  have h1 : fermatChart0ToCurve n ≫ psiFixed n T =
      chartMorphism0 (R := R n) (psiChart0Coord n T) := psiFixed_ι_false n T
  rw [phiFixedL, ← Category.assoc, h1]
  rw [show chartMorphism0 (R := R n) (psiChart0Coord n T) =
      Spec.map (CommRingCat.ofHom (evalAt (R := R n) (psiChart0Coord n T))) ≫ localChart0
      from rfl]
  rw [Category.assoc, hPolyL_lambda_chart h hh]
  rw [specMap_chartMorphism0 (R := Polynomial ℚ) (S := R n)
    (evalAt (R := R n) (psiChart0Coord n T)) (by exact RingHom.ext_rat _ _) h]

/-- Point-level form of `phiFixedL_chart0_eq`: a point of the first chart is sent to the
lambda-chart point of coordinate `h(u)`. -/
theorem phiFixedL_chart0_apply (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (x : fermatChart0Scheme n) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base x) =
      localChart0.base (PrimeSpectrum.comap
        (evalAt (R := R n) (evalAt (R := R n) (psiChart0Coord n T) h)) x) := by
  have hx := congrArg (fun g : fermatChart0Scheme n ⟶ projectiveLineGlued => g.base x)
    (phiFixedL_chart0_eq n T h hh)
  simpa only [Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom, chartMorphism0]
    using hx

/-! ## 2. The first-chart fibre over a lambda-chart closed point -/

/-- **First-chart fibre bound.** Over a point `y` of the lambda chart whose closed coordinate
is `c` (`X - C c ∈ y`), the first-chart part of the `phiFixedL`-fibre is contained in the
zero set of `h - C c` at `u = psiChart0Coord`.  This is the chart-swap counterpart of
`chart0_fibre_subset` (where the condition was `hRev(u) - c·u^d`). -/
theorem phiFixedL_chart0_fibre_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (c : ℚ) (y : PrimeSpectrum (Polynomial ℚ))
    (hy : Polynomial.X - Polynomial.C c ∈ y.asIdeal) :
    {x : fermatChart0Scheme n |
        phiFixedL n T h hh ((fermatChart0ToCurve n).base x) = localChart0.base y}
      ⊆ {x : fermatChart0Scheme n | gHom n T (h - Polynomial.C c) ∈ x.asIdeal} := by
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [phiFixedL_chart0_apply] at hx
  have hinj : Function.Injective localChart0 := localChart0.isOpenEmbedding.injective
  have hEq : PrimeSpectrum.comap
      (evalAt (R := R n) (evalAt (R := R n) (psiChart0Coord n T) h)) x = y := hinj hx
  have h1 : Polynomial.X - Polynomial.C c ∈
      (PrimeSpectrum.comap
        (evalAt (R := R n) (evalAt (R := R n) (psiChart0Coord n T) h)) x).asIdeal := by
    rw [hEq]
    exact hy
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
  rw [map_sub, Mzk1G1ProjectiveLineTransitionActual.evalAt_X,
    Mzk1G1ProjectiveLineTransitionActual.evalAt_C] at h1
  rw [← evalAt_gHom_eq n T (h - Polynomial.C c)]
  rw [map_sub, Mzk1G1ProjectiveLineTransitionActual.evalAt_C]
  exact h1

/-- **First-chart fibre finiteness.** For nonconstant `h` and `T ≠ ∅`, the first-chart part
of the `phiFixedL`-fibre over any lambda-chart point of rational coordinate `c` is finite:
the ring level statement `finite_primes_of_gHom_poly` applied to `h - C c ≠ 0`. -/
theorem phiFixedL_chart0_fiber_finite (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (hT : T.Nonempty) (hdeg : 0 < h.natDegree) (c : ℚ)
    (y : PrimeSpectrum (Polynomial ℚ)) (hy : Polynomial.X - Polynomial.C c ∈ y.asIdeal) :
    {x : fermatChart0Scheme n |
        phiFixedL n T h hh ((fermatChart0ToCurve n).base x) = localChart0.base y}.Finite :=
  (finite_primes_of_gHom_poly n T hT (h - Polynomial.C c) (sub_C_ne_zero hdeg c)).subset
    (phiFixedL_chart0_fibre_subset n T h hh c y hy)

/-! ## 3. Chart-coordinate finite-primes input (A-4 template, general value c)

The two statements below record the *ring-level* finiteness input of the A-4 route in the chart
coordinates used above: they are the chart-coordinate instantiation u = psiChart0Coord n T of
the general-value template Mzk1G1PsiFiberTemplateActual.finite_primes_of_coord (and of its
q = 0 specialisation Mzk1G1PsiPhiFixedLZeroFiberActual.finite_primes_of_coord_zero).

**Provenance of the hypothesis.**  The Module.Finite ℚ (R n ⧸ span {u - c}) input is *not*
discharged here: it is the explicit parameter of the A-4 template.  The intended discharge is the
gHom/protected-divisor computation of Mzk1G1PsiProtectedDivisorFiniteActual
(psiChart0Coord_singleton + protectedDivisor_quot_finite), or the finite_primes_of_gHom_poly
route already used for the fibre itself in phiFixedL_chart0_fiber_finite.  Note the fibre
condition of section 2 is h(u) = c (a gHom-polynomial condition), *not* u = c: these lemmas
serve the coordinate- (rather than polynomial-) shape consumers of the template. -/

/-- **Chart-coordinate finite-primes at the value c**: the points of the first chart of Y_n
where the chart coordinate u = psiChart0Coord n T equals the rational number c are finite,
provided R n ⧸ (u - c) is finite over ℚ (explicit A-4 input, see the section comment). -/
theorem finite_primes_of_chart0_value (n : Nat) (T : Finset ℚ) (c : ℚ)
    (hfin : Module.Finite ℚ (R n ⧸ Ideal.span
      ({psiChart0Coord n T - algebraMap ℚ (R n) c} : Set (R n)))) :
    {p : PrimeSpectrum (R n) |
      (psiChart0Coord n T - algebraMap ℚ (R n) c) ∈ p.asIdeal}.Finite :=
  Mzk1G1PsiFiberTemplateActual.finite_primes_of_coord
    (R := R n) (psiChart0Coord n T) c hfin

/-- **Chart-coordinate finite-primes at the value 0** (lambda = 0): the points of the first
chart of Y_n where u = psiChart0Coord n T vanishes are finite, provided R n ⧸ (u) is finite
over ℚ (explicit A-4 input). -/
theorem finite_primes_of_chart0_zero (n : Nat) (T : Finset ℚ)
    (hfin : Module.Finite ℚ (R n ⧸ Ideal.span ({psiChart0Coord n T} : Set (R n)))) :
    {p : PrimeSpectrum (R n) | psiChart0Coord n T ∈ p.asIdeal}.Finite :=
  Mzk1G1PsiPhiFixedLZeroFiberActual.finite_primes_of_coord_zero
    (R := R n) (psiChart0Coord n T) hfin

/-! ## Axiom checks -/

#print axioms phiFixedL_chart0_eq
#print axioms phiFixedL_chart0_apply
#print axioms phiFixedL_chart0_fibre_subset
#print axioms phiFixedL_chart0_fiber_finite
#print axioms finite_primes_of_chart0_value
#print axioms finite_primes_of_chart0_zero

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChart0Actual
