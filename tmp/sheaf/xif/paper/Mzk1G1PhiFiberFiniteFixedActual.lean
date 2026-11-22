/-
# B1 (owner emmy lane): scheme-level fibre finiteness of the *chart-corrected*
phiFixed = psiFixed ; hPoly

Mzk1G1PsiB1FixedActual.phiFixed n T h hh = psiFixed n T ≫ hPoly h hh is the B1/B2
morphism Y_n ⟶ P^1 built from the *swapped* two-section map psiFixed
(Mzk1G1PsiFixedActual).  This file is the psiFixed counterpart of grace's
Mzk1G1PhiFiberFiniteActual (which treats the older phi = psi ≫ hPoly).

## Chart directions (Lead ruling, do not re-derive)

psiFixed swaps the two chart assignments of psi:

* first Fermat chart (fermatChart0ToCurve, coordinate u = psiChart0Coord n T) maps to the
  **lambda-chart** of P^1 with lambda = u (chartMorphism0 u, psiFixed_ι_false);
* second piece (qPiece n T, coordinate v = psiChartInfCoord n T) maps to the
  **t-chart** of P^1 with t = v (chartMorphismInf v, psiFixed_ι_true).

hPoly is the endomorphism of P^1 whose *t-chart* piece is t ↦ h(t) (hPoly_ι_c0,
hPolyChartOf h HIdx.c0 = chartMorphismInf h); in lambda coordinates it is
lambda ↦ 1/h(1/lambda) (pieces c1/c2 with hPolyT = lambda^{-d} hRev(lambda),
hPolyLam = lambda^d/hRev(lambda)).  Consequently

* on the second piece of Y_n: t = v ↦ h(v)  (phiFixed_chartInf_eq);
* on the first piece of Y_n: lambda = u ↦ 1/h(1/u).  On the principal open D(u) of Y_n
  the target is the *t-chart* point t = h(1/u) = u^{-d} hRev(u)
  (phiFixed_chart0_local_notMem).  This is where the chart swap enters: the old phi had
  t = h(u).

## What is proved here

1. hRev_ne_zero, hRev_sub_C_mul_X_pow_ne_zero and the ring-level finiteness statements
   finite_primes_of_gHom_hRev_sub, finite_primes_of_gHom_sub_C (reusing grace's general
   finite_primes_of_gHom_poly); these are exactly the polynomial conditions that the
   first chart of phiFixed imposes over a closed point of P^1.
2. phiFixed_chartInf_eq / phiFixed_chartInf_apply: the second piece of Y_n maps by
   t = v ↦ h(v).
3. phiFixed_chart0_local_notMem / phiFixed_chart0_local_notMem_apply: the first piece of
   Y_n over D(u) maps by the t-chart coordinate h(1/u).
4. phiFixed_fiber_subset: the whole fibre of phiFixed over any point q is covered by
   (the first chart image of) the first-chart fibre together with the *fixed* finite
   r = 0 locus of qPiece; hence only the first chart of Y_n carries q-dependence
   (grace's reduction, transported to phiFixed).

## Remaining steps (handoff; see section 5 of this file for the precise recipe)

(a) ring level: finiteness of {p : PrimeSpectrum (R n) | chartX n - algebraMap ℚ (R n) t ∈ p}
    (equivalently Module.Finite ℚ (R n ⧸ (chartX - t))), i.e. finiteness of the protected
    divisor D_T = {u ∈ p}; needed only for the fibre over lambda = 0.
(b) the u ∈ x branch of the first chart (D(hRev u), hPoly piece c2), giving the polynomial
    hRev(u) - a·u^d (resp. u^d - a·hRev(u)) condition.
(c) the boundary-point bookkeeping p1Zero / p1One / p1Infinity
    (Mzk1G1PsiP1ZeroJudgeActual supplies the lambda = 0 dictionary).

No sorry, no admit, no new axioms.

OWNER: emmy lane (B1).  Do not edit Mzk1G1PsiCoverActual.lean (andrew) or
Mzk1G1PsiHPolyFinalActual.lean (henry).
-/
import tmp.sheaf.xif.paper.Mzk1G1PhiFiberFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1PsiB1FixedActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1ZeroJudgeActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFiberFiniteFixedActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartFiniteGActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiQuotientFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyCoverAlgebraActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFiberFiniteActual
open scoped AlgebraicGeometry

/-! ## 1. Ring level: the polynomial conditions of the first chart -/

/-- The reverse polynomial of a nonzero h is nonzero (its constant coefficient is
h.leadingCoeff). -/
theorem hRev_ne_zero (h : Polynomial ℚ) (hh : h ≠ 0) :
    Mzk1G1PsiHPolyActual.hRev h ≠ 0 := by
  intro h0
  have hcoeff : (Mzk1G1PsiHPolyActual.hRev h).coeff 0 = 0 := by
    rw [h0]
    simp
  rw [hRev_coeff_zero (h := h)] at hcoeff
  exact (Polynomial.leadingCoeff_ne_zero).mpr hh hcoeff

/-- hRev h - C c * X^d is nonzero for 0 < d = h.natDegree (constant coefficient
h.leadingCoeff). -/
theorem hRev_sub_C_mul_X_pow_ne_zero (h : Polynomial ℚ) (hh : h ≠ 0)
    (hdeg : 0 < h.natDegree) (c : ℚ) :
    Mzk1G1PsiHPolyActual.hRev h - Polynomial.C c * Polynomial.X ^ h.natDegree ≠ 0 := by
  intro hzero
  have hcoeff : (Mzk1G1PsiHPolyActual.hRev h - Polynomial.C c * Polynomial.X ^ h.natDegree).coeff 0
      = 0 := by
    rw [hzero]
    simp
  rw [Polynomial.coeff_sub, hRev_coeff_zero (h := h)] at hcoeff
  have hX : (Polynomial.C c * Polynomial.X ^ h.natDegree : Polynomial ℚ).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  rw [hX, sub_zero] at hcoeff
  exact (Polynomial.leadingCoeff_ne_zero).mpr hh hcoeff

/-- **Ring level, t-chart target**: for c ∈ ℚ only finitely many primes of the first
Fermat chart contain h(1/u) - c, written as the polynomial condition
hRev(u) - c·u^d.  This is the polynomial that the D(u)-branch of the first chart of
phiFixed imposes over the t-chart point of coordinate c. -/
theorem finite_primes_of_gHom_hRev_sub (n : Nat) (T : Finset ℚ) (hT : T.Nonempty)
    (h : Polynomial ℚ) (hh : h ≠ 0) (hdeg : 0 < h.natDegree) (c : ℚ) :
    {x : PrimeSpectrum (R n) |
      gHom n T (Mzk1G1PsiHPolyActual.hRev h - Polynomial.C c * Polynomial.X ^ h.natDegree)
        ∈ x.asIdeal}.Finite :=
  Mzk1G1PhiFiberFiniteActual.finite_primes_of_gHom_poly n T hT _
    (hRev_sub_C_mul_X_pow_ne_zero h hh hdeg c)

/-- **Ring level, lambda-chart target**: only finitely many primes of the first Fermat
chart contain u - a (a ∈ ℚ); this bounds the fibre of the chart coordinate
u = psiChart0Coord over a value a. -/
theorem finite_primes_of_gHom_sub_C (n : Nat) (T : Finset ℚ) (hT : T.Nonempty) (a : ℚ) :
    {x : PrimeSpectrum (R n) |
      gHom n T (Polynomial.X - Polynomial.C a) ∈ x.asIdeal}.Finite :=
  Mzk1G1PhiFiberFiniteActual.finite_primes_of_gHom_poly n T hT _
    (Polynomial.monic_X_sub_C a).ne_zero

/-! ## 2. The second piece of Y_n: t = v ↦ h(v) -/

/-- **phiFixed on the second piece** (qPiece, coordinate v): the target is the t-chart
point t = h(v), since hPoly's t-chart piece is chartMorphismInf h (hPoly_ι_c0). -/
theorem phiFixed_chartInf_eq (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    qPiece n T ≫ Mzk1G1PsiB1FixedActual.phiFixed n T h hh =
      Spec.map (CommRingCat.ofHom
          (evalAt (R := psiChartInfDomain n T) (psiChartInfCoord n T))) ≫
        chartMorphismInf (R := Polynomial ℚ) h := by
  have hkey : localChartInf ≫ hPoly h hh = chartMorphismInf (R := Polynomial ℚ) h :=
    hPoly_ι_c0 h hh
  have h1 : qPiece n T ≫ Mzk1G1PsiB1FixedActual.phiFixed n T h hh
      = chartMorphismInf (R := psiChartInfDomain n T) (psiChartInfCoord n T) ≫ hPoly h hh :=
    Mzk1G1PsiB1FixedActual.phiFixed_ι_true n T h hh
  calc qPiece n T ≫ Mzk1G1PsiB1FixedActual.phiFixed n T h hh
      = chartMorphismInf (R := psiChartInfDomain n T) (psiChartInfCoord n T) ≫ hPoly h hh := h1
    _ = (Spec.map (CommRingCat.ofHom
            (evalAt (R := psiChartInfDomain n T) (psiChartInfCoord n T))) ≫
          localChartInf) ≫ hPoly h hh := rfl
    _ = Spec.map (CommRingCat.ofHom
            (evalAt (R := psiChartInfDomain n T) (psiChartInfCoord n T))) ≫
          (localChartInf ≫ hPoly h hh) := Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom
            (evalAt (R := psiChartInfDomain n T) (psiChartInfCoord n T))) ≫
          chartMorphismInf (R := Polynomial ℚ) h := by rw [hkey]

/-- Point-level form of phiFixed_chartInf_eq. -/
theorem phiFixed_chartInf_apply (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (P : PrimeSpectrum (psiChartInfDomain n T)) :
    Mzk1G1PsiB1FixedActual.phiFixed n T h hh ((qPiece n T).base P) =
      localChartInf.base (PrimeSpectrum.comap (evalAt (R := Polynomial ℚ) h)
        (PrimeSpectrum.comap (evalAt (R := psiChartInfDomain n T) (psiChartInfCoord n T)) P)) := by
  have hpt := congrArg (fun g => g.base P) (phiFixed_chartInf_eq n T h hh)
  simpa only [Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom, chartMorphismInf]
    using hpt

/-! ## 3. The first piece of Y_n over D(u): t = h(1/u) -/

/-- The first Fermat chart localized at the protected product u = psiChart0Coord. -/
noncomputable abbrev chart0ULoc (n : Nat) (T : Finset ℚ) : Type :=
  Localization.Away (psiChart0Coord n T)

/-- The localized lambda-chart point of coordinate u is the t-chart point of coordinate
u⁻¹ (chartMorphism_transition), with the inverse written as Away.invSelf. -/
theorem chartMorphism0_algebraMap_invSelf (n : Nat) (T : Finset ℚ) :
    chartMorphism0 (R := chart0ULoc n T)
        (algebraMap (R n) (chart0ULoc n T) (psiChart0Coord n T)) =
      chartMorphismInf (R := chart0ULoc n T)
        (IsLocalization.Away.invSelf (x := psiChart0Coord n T)) := by
  have hunit : IsUnit (algebraMap (R n) (chart0ULoc n T) (psiChart0Coord n T)) :=
    IsLocalization.Away.algebraMap_isUnit (S := chart0ULoc n T) (x := psiChart0Coord n T)
  have hUval : (hunit.unit : chart0ULoc n T) =
      algebraMap (R n) (chart0ULoc n T) (psiChart0Coord n T) := IsUnit.unit_spec hunit
  have hmul : (algebraMap (R n) (chart0ULoc n T) (psiChart0Coord n T)) *
      IsLocalization.Away.invSelf (x := psiChart0Coord n T) = 1 :=
    IsLocalization.Away.mul_invSelf (x := psiChart0Coord n T)
  have hinv : (((hunit.unit)⁻¹ : (chart0ULoc n T)ˣ) : chart0ULoc n T) =
      IsLocalization.Away.invSelf (x := psiChart0Coord n T) := by
    calc (((hunit.unit)⁻¹ : (chart0ULoc n T)ˣ) : chart0ULoc n T)
        = (((hunit.unit)⁻¹ : (chart0ULoc n T)ˣ) : chart0ULoc n T) * 1 := (mul_one _).symm
      _ = (((hunit.unit)⁻¹ : (chart0ULoc n T)ˣ) : chart0ULoc n T) *
            ((hunit.unit : chart0ULoc n T) *
              IsLocalization.Away.invSelf (x := psiChart0Coord n T)) := by
          rw [hUval, hmul]
      _ = ((((hunit.unit)⁻¹ : (chart0ULoc n T)ˣ) : chart0ULoc n T) *
              (hunit.unit : chart0ULoc n T)) *
            IsLocalization.Away.invSelf (x := psiChart0Coord n T) := by rw [mul_assoc]
      _ = 1 * IsLocalization.Away.invSelf (x := psiChart0Coord n T) := by rw [Units.inv_mul]
      _ = IsLocalization.Away.invSelf (x := psiChart0Coord n T) := one_mul _
  rw [← hUval, chartMorphism_transition (R := chart0ULoc n T) hunit.unit, hinv]

/-- **phiFixed on the first piece over D(u)**: after inverting u = psiChart0Coord the
lambda-chart point of coordinate u *is* the t-chart point of coordinate u⁻¹
(chartMorphism_transition), so hPoly (which is t ↦ h(t) on its t-chart piece) acts by
t = h(u⁻¹).  This is the chart-swap counterpart of grace's phi_chart0_eq, where the
unswapped psi produced t = h(u). -/
theorem phiFixed_chart0_local_notMem (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    Spec.map (CommRingCat.ofHom (algebraMap (R n) (chart0ULoc n T))) ≫
        (fermatChart0ToCurve n ≫ Mzk1G1PsiB1FixedActual.phiFixed n T h hh) =
      Spec.map (CommRingCat.ofHom
          (evalAt (R := chart0ULoc n T)
            (IsLocalization.Away.invSelf (x := psiChart0Coord n T)))) ≫
        chartMorphismInf (R := Polynomial ℚ) h := by
  have hρ : (algebraMap (R n) (chart0ULoc n T)).comp (algebraMap ℚ (R n)) =
      algebraMap ℚ (chart0ULoc n T) :=
    RingHom.ext (fun r => IsScalarTower.algebraMap_apply ℚ (R n) (chart0ULoc n T) r)
  have hkey : localChartInf ≫ hPoly h hh = chartMorphismInf (R := Polynomial ℚ) h :=
    hPoly_ι_c0 h hh
  have h1 : fermatChart0ToCurve n ≫ Mzk1G1PsiB1FixedActual.phiFixed n T h hh
      = chartMorphism0 (R := R n) (psiChart0Coord n T) ≫ hPoly h hh :=
    Mzk1G1PsiB1FixedActual.phiFixed_ι_false n T h hh
  calc Spec.map (CommRingCat.ofHom (algebraMap (R n) (chart0ULoc n T))) ≫
        (fermatChart0ToCurve n ≫ Mzk1G1PsiB1FixedActual.phiFixed n T h hh)
      = Spec.map (CommRingCat.ofHom (algebraMap (R n) (chart0ULoc n T))) ≫
          (chartMorphism0 (R := R n) (psiChart0Coord n T) ≫ hPoly h hh) := by rw [h1]
    _ = (Spec.map (CommRingCat.ofHom (algebraMap (R n) (chart0ULoc n T))) ≫
          chartMorphism0 (R := R n) (psiChart0Coord n T)) ≫ hPoly h hh :=
        (Category.assoc _ _ _).symm
    _ = chartMorphism0 (R := chart0ULoc n T)
          (algebraMap (R n) (chart0ULoc n T) (psiChart0Coord n T)) ≫ hPoly h hh := by
        rw [specMap_chartMorphism0 (ρ := algebraMap (R n) (chart0ULoc n T)) (hρ := hρ)]
    _ = chartMorphismInf (R := chart0ULoc n T)
          (IsLocalization.Away.invSelf (x := psiChart0Coord n T)) ≫ hPoly h hh := by
        rw [chartMorphism0_algebraMap_invSelf n T]
    _ = (Spec.map (CommRingCat.ofHom
            (evalAt (R := chart0ULoc n T)
              (IsLocalization.Away.invSelf (x := psiChart0Coord n T)))) ≫
          localChartInf) ≫ hPoly h hh := rfl
    _ = Spec.map (CommRingCat.ofHom
            (evalAt (R := chart0ULoc n T)
              (IsLocalization.Away.invSelf (x := psiChart0Coord n T)))) ≫
          (localChartInf ≫ hPoly h hh) := Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom
            (evalAt (R := chart0ULoc n T)
              (IsLocalization.Away.invSelf (x := psiChart0Coord n T)))) ≫
          chartMorphismInf (R := Polynomial ℚ) h := by rw [hkey]

/-- Point-level form of phiFixed_chart0_local_notMem: for a point of the first Fermat
chart lying in D(u) (i.e. u ∉ x, witnessed by x' in the localization), phiFixed sends it
to the t-chart point t = h(1/u). -/
theorem phiFixed_chart0_local_notMem_apply (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (x : fermatChart0Scheme n) (x' : PrimeSpectrum (chart0ULoc n T))
    (hx : PrimeSpectrum.comap (algebraMap (R n) (chart0ULoc n T)) x' = x) :
    Mzk1G1PsiB1FixedActual.phiFixed n T h hh ((fermatChart0ToCurve n).base x) =
      localChartInf.base (PrimeSpectrum.comap (evalAt (R := Polynomial ℚ) h)
        (PrimeSpectrum.comap (evalAt (R := chart0ULoc n T)
          (IsLocalization.Away.invSelf (x := psiChart0Coord n T))) x')) := by
  have hpt := congrArg (fun g => g.base x') (phiFixed_chart0_local_notMem n T h hh)
  simpa only [Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom, chartMorphismInf,
    hx] using hpt

/-! ## 4. Reduction of the fibre to the first chart plus the fixed r = 0 locus -/

/-- **The fibre of phiFixed is covered by the first chart and the r = 0 locus.**
This is grace's fibre_subset transported to phiFixed; the proof only uses the two-piece
cover of Y_n and the fact that a point of the second chart with r ≠ 0 already lies in the
first chart.  Consequently the q-dependence of the fibre sits entirely in the first
chart, while the second chart contributes the *fixed* set {r = 0} (finite by
finite_primes_chartR). -/
theorem phiFixed_fiber_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (q : projectiveLineGlued) :
    (Mzk1G1PsiB1FixedActual.phiFixed n T h hh).base ⁻¹' {q} ⊆
      (fermatChart0ToCurve n).base '' ((fermatChart0ToCurve n).base ⁻¹'
        ((Mzk1G1PsiB1FixedActual.phiFixed n T h hh).base ⁻¹' {q}))
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
      obtain ⟨x, hx⟩ := Mzk1G1PhiFiberFiniteActual.qPiece_mem_range_chart0 n T P hP'
      refine ⟨x, ?_, hx⟩
      show (Mzk1G1PsiB1FixedActual.phiFixed n T h hh).base
        ((fermatChart0ToCurve n).base x) = q
      rw [hx]
      exact hz

/-- **Consumer interface for B1**: a finite bound on the *first chart* part of the fibre of
phiFixed over q makes the whole fibre finite.  The second chart contributes only the fixed
locus r = 0, which is finite by finite_primes_chartR (scoped: 0 < n).  All q-dependence is
therefore concentrated in the first-chart input S. -/
theorem phiFixed_fiber_finite_of_chart0 (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (q : projectiveLineGlued) (S : Set (PrimeSpectrum (R n)))
    (hS : S.Finite)
    (hsub : (fermatChart0ToCurve n).base ⁻¹'
      ((Mzk1G1PsiB1FixedActual.phiFixed n T h hh).base ⁻¹' {q}) ⊆ S) :
    ((Mzk1G1PsiB1FixedActual.phiFixed n T h hh).base ⁻¹' {q}).Finite := by
  have hS1 : {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
      algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
        P.asIdeal}.Finite :=
    Mzk1G1PhiFiberFiniteActual.finite_primes_chartR n T hn
  have hU : (((fermatChart0ToCurve n).base '' S) ∪
      ((qPiece n T).base '' {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
        algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
          P.asIdeal})).Finite :=
    (hS.image (fermatChart0ToCurve n).base).union (hS1.image (qPiece n T).base)
  refine hU.subset ?_
  intro z hz
  rcases phiFixed_fiber_subset n T h hh q hz with h1 | h1
  · obtain ⟨y, hy, rfl⟩ := h1
    exact Or.inl ⟨y, hsub hy, rfl⟩
  · exact Or.inr h1

/-! ## 5. Handoff: the remaining steps of the adaptation (no placeholders below)

phiFixed_fiber_subset reduces both target theorems to the **first chart** of Y_n:

  (phiFixed.base ⁻¹' {q}) ⊆ chart0 '' (chart0 ⁻¹' (phiFixed.base ⁻¹' {q})) ∪ (fixed finite set)

For a point x of the first chart put u = psiChart0Coord n T and y = comap (evalAt u) x
(a point of the lambda-chart of P^1).  Since hRev h = C (h.leadingCoeff) + X * g
(span_X_hRev_eq_top), one has hRev(u) = h.leadingCoeff + u·(…), so u ∈ x forces
hRev(u) ∉ x; hence D(u) ∪ D(hRev u) = ⊤ on Spec (R n).  The two branches are:

* u ∉ x: phiFixed_chart0_local_notMem_apply gives the t-chart point t = u^{-d} hRev(u).
  Over the t-chart closed point t = c (c ∈ ℚ) this yields hRev(u) - c·u^d ∈ x (multiply
  t - c ∈ x' by u^d); over the lambda-chart closed point lambda = a with a ≠ 0 it yields
  a·hRev(u) - u^d ∈ x.  Both sets of primes are finite by
  finite_primes_of_gHom_hRev_sub (and its a-scaled variant).
* u ∈ x: hPoly is read on its piece c2 (D(hRev) inside the lambda-chart, hPoly_ι_c2),
  whose chart map is chartMorphism0 (hPolyLam h) with
  hPolyLam h * algebraMap (hRev h) = X^d.  The same multiplication trick then gives the
  *same* polynomial hRev(u) - c·u^d ∈ x for the t-chart target c, and
  u^d - a·hRev(u) ∈ x for the lambda-chart target a.  Note that u ∈ x already contains
  the case u = 0, i.e. the protected divisor D_T.
* the boundary lambda = 0 (p1Zero, D_T) is the one target for which the condition
  degenerates to u ∈ x (the polynomial is u^d), so it needs the ring input (a) below.
* the targets outside the lambda-chart (p1Infinity = t = 0) are handled by the t-chart
  branch with c = 0 (hRev(u) ∈ x), together with
  Mzk1G1PhiFiberFiniteActual.localChart0_chartPrime_zero_notMem (which shows that the
  lambda = 0 point is not in the t-chart, hence contributes nothing on D(u)); the
  lambda = 1 point (p1One) also lies in the t-chart (coordinate 1).

Ingredient (a), still missing as a ring lemma:
Module.Finite ℚ (R n ⧸ Ideal.span {chartX n - algebraMap ℚ (R n) t}) for t ∈ T
(mirror chartRing_finite/quot_finiteDim with the ℚ[t]-structure t ↦ chartX n instead of
t ↦ psiChart0Coord; chartY is integral over ℚ[chartX] because
chartY^n = 1 - chartX^n).  Then psiChart0Coord_mem_iff turns {u ∈ x} into the finite
union ⋃_{t ∈ T} {chartX - t ∈ x}.
-/

/-! ## Axiom checks -/

#print axioms hRev_ne_zero
#print axioms hRev_sub_C_mul_X_pow_ne_zero
#print axioms finite_primes_of_gHom_hRev_sub
#print axioms finite_primes_of_gHom_sub_C
#print axioms phiFixed_chartInf_eq
#print axioms phiFixed_chartInf_apply
#print axioms chart0ULoc
#print axioms chartMorphism0_algebraMap_invSelf
#print axioms phiFixed_chart0_local_notMem
#print axioms phiFixed_chart0_local_notMem_apply
#print axioms phiFixed_fiber_subset
#print axioms phiFixed_fiber_finite_of_chart0

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFiberFiniteFixedActual
