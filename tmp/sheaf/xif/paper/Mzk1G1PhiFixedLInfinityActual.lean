/-
# B1: the point at infinity `lambda = infinity` (`t = 0`) is *not* hit by the first chart

Because `phiFixedL` sends the first chart of `Y_n` to the **lambda** chart of `P^1`
(`phiFixedL_chart0_eq`: `lambda' = h(u)`), and the point `p1Infinity` (i.e. `t = 0`, which
is `lambda = infinity`) is **not** in the lambda chart, no first-chart point maps to
`p1Infinity`.  Consequently the whole fibre over `p1Infinity` is carried by the second piece
`qPiece`, hence — by the structural reduction `phiFixedL_fiber_subset` — by the fixed,
finite `r = 0` locus.  So the `lambda = infinity` fibre is finite with no condition on `h`
(even for constant `h`)!

This closes the third boundary input of B1 for `phiFixedL`; together with
`Mzk1G1PhiFixedLLambdaPointActual` (`lambda = 0`, `lambda = 1`) all three boundary points are
finite.

## What is proved here

1. `chartMorphism0_not_mem_p1Infinity`: no lambda-chart point is `t = 0` (the dual of
   `chartMorphismInf_not_mem_p1Zero`): a common point of the two charts lies in the overlap,
   where the coordinate is a unit, contradicting primality.
2. `phiFixedL_chart0_notMem_p1Infinity`: no first-chart point of `Y_n` maps to `p1Infinity`.
3. `phiFixedL_fiber_finite_p1Infinity`: the fibre over `p1Infinity` is finite (scoped `0 < n`).

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChart0Actual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLFiberActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLInfinityActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFiberFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open scoped AlgebraicGeometry

/-- **No lambda-chart point is the point at infinity** `t = 0`: the two charts meet exactly in
the overlap, and on the overlap the `t`-coordinate is `lambda^{-1}`, a unit; but `t = 0`
means `X ∈ p`.  (Dual of `chartMorphismInf_not_mem_p1Zero`.) -/
theorem chartMorphism0_not_mem_p1Infinity {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    (p : PrimeSpectrum R) :
    chartMorphism0 a p ∉ p1Infinity := by
  intro hmem
  rw [p1Infinity] at hmem
  obtain ⟨q, hq, hqeq⟩ := hmem
  have hqrange : localChartInf.base q ∈ localChart0.opensRange := by
    rw [hqeq]
    refine Scheme.Hom.mem_opensRange.mpr
      ⟨(Spec.map (CommRingCat.ofHom (evalAt a))).base p, ?_⟩
    rw [chartMorphism0, Scheme.Hom.comp_apply]
  have hqmem : q ∈ localChartInf ⁻¹ᵁ localChart0.opensRange := hqrange
  rw [Mzk1G1ProjectiveLineChartPreimageActual.localChartInf_preimage_localChart0] at hqmem
  obtain ⟨z, hz⟩ := Scheme.Hom.mem_opensRange.mp hqmem
  have hXq : Polynomial.X ∈ q.asIdeal := by
    change Polynomial.X - Polynomial.C (0 : ℚ) ∈ q.asIdeal at hq
    simpa using hq
  have hqcomap :
      PrimeSpectrum.comap (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) z = q := by
    rw [← hz,
      show overlapToChartInf = Spec.map (CommRingCat.ofHom
        (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing))) from rfl]
    simp only [Spec.map_apply, CommRingCat.hom_ofHom]
  have hXcomap : Polynomial.X ∈
      (PrimeSpectrum.comap (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) z).asIdeal := by
    rw [hqcomap]
    exact hXq
  have halg : (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) Polynomial.X ∈ z.asIdeal := by
    have h := hXcomap
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h
    exact h
  have hunit : IsUnit ((invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) Polynomial.X) := by
    rw [RingHom.comp_apply,
      show algebraMap (Polynomial ℚ) OverlapRing Polynomial.X = ovLambda from rfl, invAuto_ovLambda]
    exact invLambda_isUnit
  exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem (I := z.asIdeal) halg hunit)

/-- **No first-chart point of `Y_n` maps to `p1Infinity`**: the first chart lands in the lambda
chart (`lambda' = h(u)`). -/
theorem phiFixedL_chart0_notMem_p1Infinity (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (x : fermatChart0Scheme n) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base x) ∉ p1Infinity := by
  rw [Mzk1G1PhiFixedLChart0Actual.phiFixedL_chart0_apply n T h hh x]
  exact chartMorphism0_not_mem_p1Infinity (R := R n)
    (evalAt (R := R n) (psiChart0Coord n T) h) x

/-- **The fibre of `phiFixedL` over `p1Infinity` is finite**, for every nonzero `h`
(no nonconstancy or nonvanishing condition): the first chart misses the point, so only the
fixed `r = 0` locus of the second chart contributes. -/
theorem phiFixedL_fiber_finite_p1Infinity (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) :
    ((phiFixedL n T h hh).base ⁻¹' p1Infinity).Finite := by
  have hpt : localChartInf.base (chartPrime 0) ∈ p1Infinity :=
    ⟨chartPrime 0, chartPrime_mem 0, rfl⟩
  have hsub : p1Infinity ⊆ {localChartInf.base (chartPrime 0)} := by
    intro z hz
    rw [p1Infinity] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    simp only [chartPoint, Set.mem_setOf_eq] at hp
    rw [chartPrime_eq_of_mem 0 p hp]
    exact Set.mem_singleton _
  refine (Mzk1G1PhiFixedLFiberActual.phiFixedL_fiber_finite_of_chart0 n T h hh hn
    (localChartInf.base (chartPrime 0)) ∅ Set.finite_empty ?_).subset
    (Set.preimage_mono hsub)
  intro x hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  rw [← hx] at hpt
  exact phiFixedL_chart0_notMem_p1Infinity n T h hh x hpt

/-! ## Axiom checks -/

#print axioms chartMorphism0_not_mem_p1Infinity
#print axioms phiFixedL_chart0_notMem_p1Infinity
#print axioms phiFixedL_fiber_finite_p1Infinity

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLInfinityActual
