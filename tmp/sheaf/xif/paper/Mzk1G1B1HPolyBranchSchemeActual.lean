/-
# B1 / O3(ii)(b): scheme-level decomposition of `hbH : Branch (hPoly h hh) ⊆ boundarySetGlued`

Consumer: `Mzk1G1B1HbObligationsActual.hb_of_branch_hPoly_subset_auto` (and hence
`Mzk1G1PhiFixedLBranchSupportActual`, the B1 branch lane).

This file decomposes the scheme-level obligation `hbH` into two named inputs and
proves that they suffice:

* (i) **value layer** (DONE, grace `Mzk1G1B1O3ValueLayerActual`):
  `Polynomial.criticalValues (S := ℂ) h ⊆ {0,1}` (`o3a_criticalValues_subset`).
  Here it is transported to the `Polynomial.aeval` derivative-zero form (`ValueLayer`)
  and, through the residue-field/Galois argument, to the prime-point form
  (`critical_prime_value_mem_or_sub_one`, `h'(λ) ∈ p → h ∈ p ∨ h - 1 ∈ p`).
* (ii) **scheme bridge** (**the remaining O3(ii)(b) obligation**): every point of
  `Branch (hPoly h hh)` is the image, under the `t`-chart parametrisation, of a
  derivative-zero prime (`hpts`, an explicit parameter).

## What is proved here (no sorry, no new axiom)

1. `hPoly_chartInf_apply`, `hPoly_chartInf_apply_aeval`, `hPoly_chart0_apply`:
   the point formula of `hPoly` on the `t`-chart (`t ↦ h(t)`), in `evalAt` /
   `Polynomial.aeval` form.
2. `derivativeZeroSet`, `ram_hPoly_inter_chart0_eq`, `hPoly_ram_subset_derivative`:
   the part of `Ram (hPoly)` lying over the `t`-chart is exactly the image of
   `Ram (chartMorphismInf h)`, and (given the explicit bridge `hbridge`) it lands in the
   derivative-zero set.
3. `ValueLayer`, `valueLayer_of_o3a`, `valueLayer_of_criticalValues`,
   `critical_prime_value_mem_or_sub_one`, `hbH_of_value_and_ram`, `hbH_of_value_data`,
   `hbH_of_M2AnalyticTarget`: the O3(ii)(b) **reduction**.
4. `locallyOfFinitePresentation_specMap`, `locallyOfFinitePresentation_chartMorphismInf`,
   `hPoly_locallyOfFinitePresentation_of_charts`, `hPolyL_locallyOfFinitePresentation`:
   the O4 reduction (three chart pieces + `OpenCover` localisation), and the O5 statement
   for `hPolyL`.

## Explicit obligations (NOT closed here)

* `hpts` (remaining O3(ii)(b)): `Branch (hPoly h hh) ⊆ chartMorphismInf h '' derivativeZeroSet h`.
  Proof plan: `Ram` is closed (`BelyiRamification.isClosed_ram`), the `t`-chart is an
  open piece (`localChartInf_isOpenImmersion`), and `hPoly` is glued from its chart
  morphisms (`hPoly_ι_c0`); combine `ram_hPoly_inter_chart0_eq` with a description of
  `Branch` on the other chart pieces (`hPoly_ι_c1`, `hPoly_ι_c2`, whose coordinates are
  `hPolyT` and `hPolyLam`).
* `hbridge` (the derivative half of O3(ii)(b), see `hPoly_ram_subset_derivative`):
  `Ram (chartMorphismInf h) ⊆ derivativeZeroSet h`. Proof plan: `Ram f = (f.smoothLocus)ᶜ`
  (definition of `BelyiRamification.Ram`), and
  `chartMorphismInf h = Spec.map (evalAt h) ≫ localChartInf` with `localChartInf` an open
  immersion, so the smooth locus agrees with that of `Spec.map (evalAt h)`
  (`Scheme.Hom.preimage_smoothLocus_eq`); then `Spec.map (evalAt h)` is smooth at `p`
  iff `RingHom.FormallySmooth (stalkMap)` iff `h'(λ) ∉ p` (the Kähler differential of
  `ℚ[λ] → ℚ[λ]`, `λ ↦ h(λ)`, is `dλ ↦ h'(λ) dλ`, locally free iff the derivative
  is invertible at `p`). The tree contains no scheme-level "derivative zero ⇔ not smooth"
  bridge yet, so it is kept as an explicit parameter.
* `[LocallyOfFinitePresentation (hPoly h hh)]` (O4): the geometric half is proved here
  (`hPoly_locallyOfFinitePresentation_of_charts`), what is missing is the ring-theoretic input
  `RingHom.FinitePresentation (evalAt a)` (finiteness of presentation of the substitution
  algebra `a ↦ h(a)`); plan in the docstring of that declaration.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1BelyiRamificationActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyFinalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChartInfBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChart0Actual
import tmp.sheaf.xif.paper.Mzk1G1B1O3ValueLayerActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1InvBoundaryActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyBranchSchemeActual

open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChartInfBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1O3ValueLayerActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvBoundaryActual

/-! ## 0. The `evalAt` / `Polynomial.aeval` dictionary -/

/-- `evalAt a` is the ring hom underlying the algebra map `Polynomial.aeval a`: both send
`λ` to `a`. -/
theorem evalAt_eq_aeval {R : Type} [CommRing R] [Algebra ℚ R] (a : R) (p : Polynomial ℚ) :
    Mzk1G1ProjectiveLineTransitionActual.evalAt a p = Polynomial.aeval a p := rfl

/-! ## 1. The point formula of `hPoly` on the `t`-chart -/

/-- **`hPoly` on the `t`-chart**: `t ↦ h(t)`.
For any `ℚ`-algebra `R`, a coordinate `a : R` and a prime `p`, `hPoly h hh` sends
the `t`-chart point of coordinate `a` to the `t`-chart point of coordinate
`evalAt a h = h(a)`. Donor: `chartMorphismInf_comp_hPoly`. -/
theorem hPoly_chartInf_apply {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    (h : Polynomial ℚ) (hh : h ≠ 0) (p : PrimeSpectrum R) :
    (hPoly h hh).base ((chartMorphismInf (R := R) a).base p) =
      (chartMorphismInf (R := R) (Mzk1G1ProjectiveLineTransitionActual.evalAt a h)).base p := by
  have hcomp := chartMorphismInf_comp_hPoly (R := R) a h hh
  calc (hPoly h hh).base ((chartMorphismInf (R := R) a).base p)
      = ((chartMorphismInf (R := R) a) ≫ hPoly h hh).base p := by
        rw [Scheme.Hom.comp_apply]
    _ = (chartMorphismInf (R := R) (Mzk1G1ProjectiveLineTransitionActual.evalAt a h)).base p := by
        rw [hcomp]

/-- The same point formula in `Polynomial.aeval` form: the `t`-coordinate of the image is
`Polynomial.aeval a h`. -/
theorem hPoly_chartInf_apply_aeval {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    (h : Polynomial ℚ) (hh : h ≠ 0) (p : PrimeSpectrum R) :
    (hPoly h hh).base ((chartMorphismInf (R := R) a).base p) =
      (chartMorphismInf (R := R) (Polynomial.aeval a h)).base p := by
  rw [hPoly_chartInf_apply a h hh p, evalAt_eq_aeval]

/-- **`hPoly` on `P¹`'s own `t`-chart**, chart form: `hPoly` restricted to the first
piece of its cover is `chartMorphismInf h` (donor `hPoly_ι_c0`). -/
theorem hPoly_chart0_eq (h : Polynomial ℚ) (hh : h ≠ 0) :
    localChartInf ≫ hPoly h hh = chartMorphismInf (R := Polynomial ℚ) h := by
  rw [show localChartInf = (hPolyCover h hh).f HIdx.c0 from rfl]
  exact hPoly_ι_c0 h hh

/-- **Point formula of `hPoly` on `P¹`'s own `t`-chart**: for `x : Spec ℚ[t]`, the
image is the `t`-chart point whose coordinate is `h(t)`, i.e. the prime
`comap (evalAt h) x` of `ℚ[t']`. -/
theorem hPoly_chart0_apply (h : Polynomial ℚ) (hh : h ≠ 0)
    (x : PrimeSpectrum (Polynomial ℚ)) :
    (hPoly h hh).base (localChartInf.base x) =
      localChartInf.base (PrimeSpectrum.comap
        (Mzk1G1ProjectiveLineTransitionActual.evalAt (R := Polynomial ℚ) h) x) := by
  calc (hPoly h hh).base (localChartInf.base x)
      = (localChartInf ≫ hPoly h hh).base x := by rw [Scheme.Hom.comp_apply]
    _ = (chartMorphismInf (R := Polynomial ℚ) h).base x := by rw [hPoly_chart0_eq h hh]
    _ = localChartInf.base (PrimeSpectrum.comap
          (Mzk1G1ProjectiveLineTransitionActual.evalAt (R := Polynomial ℚ) h) x) :=
        chartMorphismInf_apply (R := Polynomial ℚ) h x

/-- The same, `Polynomial.aeval` form. -/
theorem hPoly_chart0_apply_aeval (h : Polynomial ℚ) (hh : h ≠ 0)
    (x : PrimeSpectrum (Polynomial ℚ)) :
    (hPoly h hh).base (localChartInf.base x) =
      localChartInf.base (PrimeSpectrum.comap (Polynomial.aeval (R := ℚ) h).toRingHom x) :=
  hPoly_chart0_apply h hh x

/-! ## 2. `Ram` on the `t`-chart and the derivative-zero set -/

/-- Equal morphisms have equal smooth loci (the smooth locus only depends on the stalk maps;
the `LocallyOfFinitePresentation` instances are proof-irrelevant). -/
theorem smoothLocus_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) :
    f.smoothLocus = g.smoothLocus := by
  refine SetLike.ext fun x => ?_
  rw [Scheme.Hom.mem_smoothLocus, Scheme.Hom.mem_smoothLocus, h]

/-- **The derivative-zero set on the `t`-chart**: the primes of `ℚ[λ]` where the
derivative of `h` vanishes. Written through `Polynomial.aeval X` so that it is the
`λ = X` instance of the value-layer formulas. -/
def derivativeZeroSet (h : Polynomial ℚ) : Set (PrimeSpectrum (Polynomial ℚ)) :=
  {q | Polynomial.aeval (R := ℚ) (Polynomial.X : Polynomial ℚ) (Polynomial.derivative h) ∈
    q.asIdeal}

/-- Membership in the derivative-zero set, in plain divisibility form. -/
theorem mem_derivativeZeroSet_iff {h : Polynomial ℚ} {q : PrimeSpectrum (Polynomial ℚ)} :
    q ∈ derivativeZeroSet h ↔ Polynomial.derivative h ∈ q.asIdeal := by
  rw [derivativeZeroSet, Set.mem_setOf_eq, Polynomial.aeval_X_left_apply]

/-- **`Ram (hPoly)` over the `t`-chart**: on the image of the `t`-chart
(`Set.range localChartInf.base`), the ramification locus of `hPoly h hh` is exactly the image
of the ramification locus of `chartMorphismInf h`.

Proof: `hPoly` restricts to `chartMorphismInf h` on the `t`-chart
(`hPoly_chart0_eq`), and `localChartInf` is an open immersion, so the smooth loci
correspond (`Scheme.Hom.preimage_smoothLocus_eq`). -/
theorem ram_hPoly_inter_chart0_eq (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)] :
    Ram (hPoly h hh) ∩ Set.range localChartInf.base =
      localChartInf.base '' Ram (chartMorphismInf (R := Polynomial ℚ) h) := by
  have hpre : localChartInf ⁻¹ᵁ (hPoly h hh).smoothLocus =
      (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq (f := localChartInf) (g := hPoly h hh)]
    exact smoothLocus_congr (hPoly_chart0_eq h hh)
  have hkey : ∀ x : chartInfScheme,
      x ∈ Ram (chartMorphismInf (R := Polynomial ℚ) h) ↔
        localChartInf.base x ∈ Ram (hPoly h hh) := by
    intro x
    have h2 : x ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus ↔
        localChartInf.base x ∈ (hPoly h hh).smoothLocus := by
      rw [← hpre]
      exact Iff.rfl
    show ¬ (x ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus) ↔
      ¬ (localChartInf.base x ∈ (hPoly h hh).smoothLocus)
    exact not_congr h2
  ext y
  constructor
  · rintro ⟨hy, ⟨x, rfl⟩⟩
    exact ⟨x, (hkey x).mpr hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(hkey x).mp hx, ⟨x, rfl⟩⟩

/-- **O3(ii)(b): the derivative half (explicit-obligation form)**.
If the ramification locus of the `t`-chart morphism `chartMorphismInf h` is contained in the
derivative-zero set (the explicit bridge `hbridge`; see the file header for its proof plan),
then the part of `Ram (hPoly h hh)` over the `t`-chart lies in the image of that set. -/
theorem hPoly_ram_subset_derivative (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hbridge : Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h) :
    Ram (hPoly h hh) ∩ Set.range localChartInf.base ⊆
      localChartInf.base '' derivativeZeroSet h := by
  rw [ram_hPoly_inter_chart0_eq h hh]
  exact Set.image_mono hbridge

/-! ## 3. The value layer (grace's O3) and its translation to primes -/

/-- **The value layer** (value half of the O3 dictionary): at every critical point of `h` in `ℂ`,
the value of `h` lies in `{0,1}`. This is exactly the third conjunct of
`M2AnalyticTarget`, i.e. grace's `o3a_aeval_of_derivative_zero`. -/
def ValueLayer (h : Polynomial ℚ) : Prop :=
  ∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative h) = 0 →
    Polynomial.aeval z h ∈ ({0, 1} : Set ℂ)

/-- The value layer, extracted from grace's `M2AnalyticTarget` (DONE, O3 value layer). -/
theorem valueLayer_of_o3a {BranchSet : Finset ℂ} (tgt : M2AnalyticTarget BranchSet) :
    ValueLayer tgt.choose :=
  fun z hz => o3a_aeval_of_derivative_zero tgt z hz

/-- The value layer in `Polynomial.criticalValues` form (grace's
`o3a_criticalValues_subset`) implies the `aeval` derivative-zero form. -/
theorem valueLayer_of_criticalValues {h : Polynomial ℚ} (hdeg : 0 < h.natDegree)
    (hcv : (Polynomial.criticalValues (S := ℂ) h) ⊆ ({0, 1} : Set ℂ)) : ValueLayer h := by
  intro z hz
  have hder : Polynomial.derivative h ≠ 0 := Polynomial.derivative_ne_zero.mpr hdeg.ne'
  exact hcv (Polynomial.aeval_mem_criticalValues ((Polynomial.mem_rootSet_of_ne hder).mpr hz))

/-- **Critical primes carry boundary values** (the "value" half of O3(ii)(b), from the value
layer). If `p` is a prime of `ℚ[λ]` containing the derivative of a nonconstant `h`,
then `h ∈ p` or `h - 1 ∈ p`.

Translation argument (no extra input beyond the value layer): `ℚ[λ]` is a principal ideal
domain and `p ≠ ⊥`, so `p = (g)` with `g` irreducible; `g ∣ h'` gives a root
`z ∈ ℂ` of `g`, hence a critical point of `h`; the value layer puts `h(z)` in
`{0,1}`, so `h - C c` (`c = h(z) ∈ ℚ`) vanishes at `z`, hence is a multiple of
`minpoly z`, which is associated to `g`; therefore `g ∣ h - C c`, i.e. `h - C c ∈ p`. -/
theorem critical_prime_value_mem_or_sub_one {h : Polynomial ℚ} (hdeg : 0 < h.natDegree)
    (hval : ValueLayer h) {q : PrimeSpectrum (Polynomial ℚ)}
    (hq : Polynomial.derivative h ∈ q.asIdeal) :
    h ∈ q.asIdeal ∨ h - 1 ∈ q.asIdeal := by
  have hder : Polynomial.derivative h ≠ 0 := Polynomial.derivative_ne_zero.mpr hdeg.ne'
  have hqne : q.asIdeal ≠ ⊥ := by
    intro hbot
    rw [hbot] at hq
    exact hder (by simpa using hq)
  haveI : q.asIdeal.IsPrincipal := inferInstance
  -- a generator `g` of `q`, which is prime hence irreducible
  obtain ⟨g, hgspan, hgprime⟩ : ∃ g : Polynomial ℚ,
      Ideal.span ({g} : Set (Polynomial ℚ)) = q.asIdeal ∧ Prime g :=
    ⟨Submodule.IsPrincipal.generator q.asIdeal,
      Ideal.span_singleton_generator q.asIdeal,
      Submodule.IsPrincipal.prime_generator_of_isPrime q.asIdeal hqne⟩
  have hg_irred : Irreducible g := hgprime.irreducible
  -- `g ∣ h'`
  have hgdvd : g ∣ Polynomial.derivative h := by
    have hmem : Polynomial.derivative h ∈ Ideal.span ({g} : Set (Polynomial ℚ)) := by
      rw [hgspan]
      exact hq
    exact Ideal.mem_span_singleton.mp hmem
  -- `g` is nonconstant, hence has a root `z` in `ℂ`
  have hgdeg : g.degree ≠ 0 := hg_irred.degree_pos.ne'
  have hinj : Function.Injective (algebraMap ℚ ℂ) := by
    intro a b hab
    exact_mod_cast hab
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (k := ℂ) hinj g hgdeg
  -- `z` is a critical point of `h`
  have hzc : Polynomial.aeval z (Polynomial.derivative h) = 0 := by
    obtain ⟨s, hs⟩ := hgdvd
    rw [hs, map_mul, hz, zero_mul]
  -- the value layer: the value at `z` is `0` or `1`
  have hzval : Polynomial.aeval z h ∈ ({0, 1} : Set ℂ) := hval z hzc
  -- `minpoly z` and `g` are associated
  set c0 : ℚ := g.leadingCoeff with hc0
  have hc0ne : c0 ≠ 0 := by
    rw [hc0]
    exact Polynomial.leadingCoeff_ne_zero.mpr hg_irred.ne_zero
  have hmin_eq : g = Polynomial.C c0 * minpoly ℚ z := by
    rw [hc0]
    exact minpoly.Irreducible.eq_minpoly hg_irred hz
  -- extract the rational value `c ∈ {0,1}`
  obtain ⟨c, hc01, hcval⟩ : ∃ c : ℚ, c ∈ ({0, 1} : Set ℚ) ∧
      Polynomial.aeval z h = algebraMap ℚ ℂ c := by
    have hcases : Polynomial.aeval z h = 0 ∨ Polynomial.aeval z h = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzval
    rcases hcases with h0 | h1
    · exact ⟨0, Or.inl rfl, by rw [h0]; simp⟩
    · exact ⟨1, Or.inr rfl, by rw [h1]; simp⟩
  -- `minpoly z ∣ h - C c`
  have hdvd : minpoly ℚ z ∣ h - Polynomial.C c :=
    minpoly.dvd ℚ z (by rw [map_sub, hcval, Polynomial.aeval_C, sub_self])
  -- hence `g ∣ h - C c`
  have hg_dvd : g ∣ h - Polynomial.C c := by
    obtain ⟨s, hs⟩ := hdvd
    refine ⟨Polynomial.C c0⁻¹ * s, ?_⟩
    have hcunit : Polynomial.C c0 * Polynomial.C c0⁻¹ = 1 := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ hc0ne, Polynomial.C_1]
    calc h - Polynomial.C c
        = minpoly ℚ z * s := hs
      _ = (Polynomial.C c0 * Polynomial.C c0⁻¹) * (minpoly ℚ z * s) := by
          rw [hcunit, one_mul]
      _ = (Polynomial.C c0 * minpoly ℚ z) * (Polynomial.C c0⁻¹ * s) := by ring
      _ = g * (Polynomial.C c0⁻¹ * s) := by rw [hmin_eq]
  -- so `h - C c` lies in `q`
  have hmem : h - Polynomial.C c ∈ q.asIdeal := by
    rw [← hgspan]
    exact Ideal.mem_span_singleton.mpr hg_dvd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc01
  rcases hc01 with rfl | rfl
  · exact Or.inl (by simpa using hmem)
  · exact Or.inr (by simpa using hmem)

/-! ## 4. The O3(ii)(b) reduction -/

/-- **O3(ii)(b) reduction (core)**: `hbH` follows from the value layer `hval` (grace's O3,
DONE) together with the explicit scheme-level bridge `hpts` (the remaining obligation: each branch
point is the `t`-chart image of a derivative-zero prime). -/
theorem hbH_of_value_and_ram (h : Polynomial ℚ) (hh : h ≠ 0) (hdeg : 0 < h.natDegree)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hval : ValueLayer h)
    (hpts : Branch (hPoly h hh) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h) :
    Branch (hPoly h hh) ⊆ boundarySetGlued := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := hpts hy
  have hq' : Polynomial.derivative h ∈ q.asIdeal := mem_derivativeZeroSet_iff.mp hq
  rw [chartMorphismInf_mem_boundarySetGlued_iff]
  exact critical_prime_value_mem_or_sub_one hdeg hval hq'

/-- **O3(ii)(b) reduction (`criticalValues` form)**: the value layer is taken in exactly the shape
of grace's `o3a_criticalValues_subset`, `Polynomial.criticalValues (S := ℂ) h ⊆ {0,1}`. -/
theorem hbH_of_value_data (h : Polynomial ℚ) (hh : h ≠ 0) (hdeg : 0 < h.natDegree)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hcv : (Polynomial.criticalValues (S := ℂ) h) ⊆ ({0, 1} : Set ℂ))
    (hpts : Branch (hPoly h hh) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h) :
    Branch (hPoly h hh) ⊆ boundarySetGlued :=
  hbH_of_value_and_ram h hh hdeg (valueLayer_of_criticalValues hdeg hcv) hpts

/-- **O3(ii)(b) reduction wired to grace's analytic target**: the only inputs are
`tgt : M2AnalyticTarget BranchSet` (whose third conjunct is the value layer, DONE) and the explicit
scheme bridge `hpts`. -/
theorem hbH_of_M2AnalyticTarget {BranchSet : Finset ℂ} (tgt : M2AnalyticTarget BranchSet)
    (hh : tgt.choose ≠ 0) (hdeg : 0 < tgt.choose.natDegree)
    [LocallyOfFinitePresentation (hPoly tgt.choose hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) tgt.choose)]
    (hpts : Branch (hPoly tgt.choose hh) ⊆
      chartMorphismInf (R := Polynomial ℚ) tgt.choose '' derivativeZeroSet tgt.choose) :
    Branch (hPoly tgt.choose hh) ⊆ boundarySetGlued :=
  hbH_of_value_and_ram tgt.choose hh hdeg (valueLayer_of_o3a tgt) hpts

/-! ## 5. O4: locality of finite presentation of `hPoly` and `hPolyL` -/

/-- `Spec.map` of a ring map of finite presentation is locally of finite presentation
(`LocallyOfFinitePresentation.SpecMap_iff`). -/
theorem locallyOfFinitePresentation_specMap {R : Type} [CommRing R] [Algebra ℚ R]
    (a : R) (hfp : RingHom.FinitePresentation
      (Mzk1G1ProjectiveLineTransitionActual.evalAt a)) :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (Mzk1G1ProjectiveLineTransitionActual.evalAt a))) := by
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  simpa using hfp

/-- A chart morphism `chartMorphismInf a` is locally of finite presentation as soon as the
coordinate map `evalAt a : ℚ[λ] → R` is of finite presentation (the other factor
`localChartInf` is an open immersion, hence locally of finite presentation). -/
theorem locallyOfFinitePresentation_chartMorphismInf {R : Type} [CommRing R] [Algebra ℚ R]
    (a : R) (hfp : RingHom.FinitePresentation
      (Mzk1G1ProjectiveLineTransitionActual.evalAt a)) :
    LocallyOfFinitePresentation (chartMorphismInf (R := R) a) := by
  haveI := locallyOfFinitePresentation_specMap a hfp
  show LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (Mzk1G1ProjectiveLineTransitionActual.evalAt a)) ≫ localChartInf)
  infer_instance

/-- **O4 reduction**: `hPoly h hh` is locally of finite presentation as soon as its three chart
pieces are (`hPolyChartOf`), by Zariski locality at the source applied to the cover
`hPolyCover h hh` and the three chart formulas `hPoly_ι_c0/c1/c2`.

Remaining ring-theoretic input (explicit obligations `H0`, `H1`, `H2`): each chart morphism is
`Spec.map (evalAt a) ≫ localChartInf` (`locallyOfFinitePresentation_chartMorphismInf`), so it
suffices to know `RingHom.FinitePresentation (evalAt a)` for `a = h`, `a = hPolyT h` (over
`Localization.Away X`) and `a = hPolyLam h` (over `Localization.Away (hRev h)`).
Plan for the missing input: `evalAt a` is the substitution `λ ↦ a`, and
`RingHom.FinitePresentation.of_finiteType` reduces (as `ℚ[λ]` is Noetherian) to finite type,
which holds because `ℚ[λ]` is generated as a `ℚ[λ]`-algebra (structure map `evalAt a`) by the
single element `λ`; localised coordinates follow from stability of finite presentation under
localisation (`RingHom.finitePresentation_stableUnderComposition` +
`RingHom.finitePresentation_holdsForLocalizationAway`). -/
theorem hPoly_locallyOfFinitePresentation_of_charts (h : Polynomial ℚ) (hh : h ≠ 0)
    (H0 : LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h))
    (H1 : LocallyOfFinitePresentation (chartMorphismInf
      (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h)))
    (H2 : LocallyOfFinitePresentation (chartMorphism0
      (R := Localization.Away (hRev h)) (hPolyLam h))) :
    LocallyOfFinitePresentation (hPoly h hh) := by
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation)
    (hPolyCover h hh)).mpr ?_
  intro i
  match i with
  | HIdx.c0 => rw [hPoly_ι_c0 h hh]; exact H0
  | HIdx.c1 => rw [hPoly_ι_c1 h hh]; exact H1
  | HIdx.c2 => rw [hPoly_ι_c2 h hh]; exact H2

/-- **O5**: `hPolyL = p1Inv ≫ hPoly ≫ p1Inv` is locally of finite presentation as soon as
`hPoly` is: `p1Inv` is an isomorphism (hence an open immersion, hence locally of
finite presentation) and the property is stable under composition. -/
theorem hPolyL_locallyOfFinitePresentation (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)] :
    LocallyOfFinitePresentation (hPolyL h hh) := by
  haveI : IsIso p1Inv := ⟨p1Inv, p1Inv_inv, p1Inv_inv⟩
  rw [hPolyL_def]
  infer_instance

/-! ## Axiom checks -/

#print axioms evalAt_eq_aeval
#print axioms hPoly_chartInf_apply
#print axioms hPoly_chartInf_apply_aeval
#print axioms hPoly_chart0_eq
#print axioms hPoly_chart0_apply
#print axioms hPoly_chart0_apply_aeval
#print axioms smoothLocus_congr
#print axioms derivativeZeroSet
#print axioms mem_derivativeZeroSet_iff
#print axioms ram_hPoly_inter_chart0_eq
#print axioms hPoly_ram_subset_derivative
#print axioms ValueLayer
#print axioms valueLayer_of_o3a
#print axioms valueLayer_of_criticalValues
#print axioms critical_prime_value_mem_or_sub_one
#print axioms hbH_of_value_and_ram
#print axioms hbH_of_value_data
#print axioms hbH_of_M2AnalyticTarget
#print axioms locallyOfFinitePresentation_specMap
#print axioms locallyOfFinitePresentation_chartMorphismInf
#print axioms hPoly_locallyOfFinitePresentation_of_charts
#print axioms hPolyL_locallyOfFinitePresentation

end LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyBranchSchemeActual
