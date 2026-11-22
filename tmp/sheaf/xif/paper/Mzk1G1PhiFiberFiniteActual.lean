/-
# Item A (grace): SCHEME-level fibre finiteness of `phi = psi ; hPoly`

`Mzk1G1PsiB1Actual.phi n T h hh = psi n T ≫ hPoly h hh : Y_n ⟶ P^1`.
Item 6 supplied the *chart level* finiteness statements (finitely many primes above a value of a
chart coordinate).  This file bridges them to the scheme-level statement that the fibre
`phi.base ⁻¹' {q}` is a finite set of points of `Y_n`.

## Adopted statement

The literal request `∀ q, (phi.base ⁻¹' {q}).Finite` is **false** without extra
conditions: for a constant `h` (`h = C c`, `c ≠ 0`) the morphism `hPoly` is the
constant morphism with target the closed point of the `t`-chart of coordinate `c`, so the
fibre of `phi` over that point is all of `Y_n`.  We therefore require
`0 < h.natDegree` (h nonconstant), and we restrict the target point to the points at which
the chart machinery of item 6 applies, namely: `q` outside the `t`-chart of `P^1`, or
`q` the closed point of the `t`-chart with a rational coordinate.  This covers the whole
boundary `{0, 1, ∞}` used by B1, and we derive
`(phi.base ⁻¹' boundarySetGlued).Finite` for the consumer.

## Route

1. `R n` is a finite `ℚ[t]`-module (`gHom : t ↦ psiChart0Coord`); hence for any nonzero
   `f ∈ ℚ[t]` only finitely many primes of `R n` contain `f (psiChart0Coord)`  (chart 0).
   The same for `R2 n` with `rHom : t ↦ chartR` and for the localization `D(q)` (chart 1).
2. On the first chart of `Y_n`, `phi` is `t ↦ h (psiChart0Coord)` followed by the
   `t`-chart inclusion of `P^1`; hence over the `t`-chart point of coordinate `c` its
   fibre sits in the zero set of the nonzero polynomial `h - C c`.
3. The image of the first chart is contained in the `t`-chart of `P^1`; and a point of the
   second chart of `Y_n` with `r ≠ 0` already lies in the first chart.  Hence the whole
   fibre is covered by the first chart image together with the `r = 0` locus of the second
   chart, and the latter contributes at most the finitely many points of `Y_n` cut out by `r`.

No placeholders, no new postulates.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiB1Actual
import tmp.sheaf.xif.paper.Mzk1G1PsiFiberFiniteInfActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFiberFiniteActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartFiniteGActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiQuotientFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberFiniteInfActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open scoped AlgebraicGeometry

/-! ## 1. Ring level: finitely many primes above a value of a chart coordinate -/

/-- **Chart 0 ring level.** Finitely many primes of the first Fermat chart contain
`f (psiChart0Coord n T)`, for `f ≠ 0`. -/
theorem finite_primes_of_gHom_poly (n : Nat) (T : Finset ℚ) (hT : T.Nonempty)
    (f : Polynomial ℚ) (hf : f ≠ 0) :
    {x : PrimeSpectrum (R n) | gHom n T f ∈ x.asIdeal}.Finite := by
  classical
  have hfin : Module.Finite ℚ (R n ⧸ Ideal.span ({gHom n T f} : Set (R n))) := by
    letI := gAlgebra n T
    exact quot_finiteDim n T hT f hf
  exact finite_primes_of_finite_quotient (f := gHom n T f) hfin

/-- **Chart 1 ring level.** Finitely many primes of the second Fermat chart contain
`f (chartR n)`, for `f ≠ 0`. -/
theorem finite_primes_of_rHom_poly (n : Nat) (hn : 0 < n) (f : Polynomial ℚ) (hf : f ≠ 0) :
    {p : PrimeSpectrum (R2 n) | rHom n f ∈ p.asIdeal}.Finite := by
  classical
  have hfin : Module.Finite ℚ (R2 n ⧸ Ideal.span ({rHom n f} : Set (R2 n))) := by
    letI := rAlgebra n
    exact quot_finiteDim_inf n hn f hf
  exact finite_primes_of_finite_quotient (f := rHom n f) hfin

/-- **Localized chart 1 ring level**: finitely many primes of `D(q)` contain the image of
`f (chartR n)`, `f ≠ 0`. -/
theorem finite_primes_of_rHom_localized (n : Nat) (T : Finset ℚ) (hn : 0 < n)
    (f : Polynomial ℚ) (hf : f ≠ 0) :
    {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
      algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (rHom n f) ∈
        P.asIdeal}.Finite := by
  classical
  have hinj : Function.Injective
      (PrimeSpectrum.comap
        (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)))) :=
    PrimeSpectrum.localization_comap_injective (Localization.Away (psiChartInfDenom n T))
      (Submonoid.powers (psiChartInfDenom n T))
  have hfin := finite_primes_of_rHom_poly n hn f hf
  have hset : {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
        algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (rHom n f) ∈ P.asIdeal}
      = PrimeSpectrum.comap (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))) ⁻¹'
        {p : PrimeSpectrum (R2 n) | rHom n f ∈ p.asIdeal} := by
    ext P
    simp [PrimeSpectrum.comap_asIdeal]
  rw [hset]
  exact Set.Finite.preimage (hinj.injOn.mono (Set.subset_univ _)) hfin

/-- **The `r = 0` locus of the second chart is finite** (`r` is the coordinate `chartR`). -/
theorem finite_primes_chartR (n : Nat) (T : Finset ℚ) (hn : 0 < n) :
    {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
      algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
        P.asIdeal}.Finite := by
  have h := finite_primes_of_rHom_localized n T hn Polynomial.X Polynomial.X_ne_zero
  rwa [rHom_X] at h

/-! ## 2. Elementary coordinate facts -/

/-- `h - C c` is nonzero for nonconstant `h`. -/
theorem sub_C_ne_zero {h : Polynomial ℚ} (hdeg : 0 < h.natDegree) (c : ℚ) :
    h - Polynomial.C c ≠ 0 := by
  intro hc
  have hc' : h = Polynomial.C c := sub_eq_zero.mp hc
  have hzero : h.natDegree = 0 := by
    rw [hc']
    exact Polynomial.natDegree_C c
  omega

/-- The chart map `evalAt h` sends `X - C c` to `h - C c`. -/
theorem evalAt_poly (h : Polynomial ℚ) (c : ℚ) :
    evalAt (R := Polynomial ℚ) h (Polynomial.X - Polynomial.C c) = h - Polynomial.C c := by
  rw [map_sub, evalAt_X, evalAt_C, ← Polynomial.C_eq_algebraMap]

/-- `evalAt` at the protected product is the structure map `gHom`. -/
theorem evalAt_gHom_eq (n : Nat) (T : Finset ℚ) (f : Polynomial ℚ) :
    evalAt (R := R n) (psiChart0Coord n T) f = gHom n T f := by
  show Polynomial.aeval (R := ℚ) (psiChart0Coord n T) f = gHom n T f
  rw [Polynomial.aeval_def]
  rfl

/-! ## 3. The first chart of the curve -/

/-- **`phi` on the first chart of `Y_n`**: the `t`-coordinate `a = psiChart0Coord`
followed by the polynomial chart map of `hPoly` (the `t`-piece, which is `localChartInf`). -/
theorem phi_chart0_eq (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    fermatChart0ToCurve n ≫ Mzk1G1PsiB1Actual.phi n T h hh =
      (Spec.map (CommRingCat.ofHom (evalAt (R := R n) (psiChart0Coord n T)))) ≫
        (Spec.map (CommRingCat.ofHom (evalAt (R := Polynomial ℚ) h))) ≫ localChartInf := by
  rw [Mzk1G1PsiB1Actual.phi, ← Category.assoc]
  have h1 : (fermatChart0ToCurve n ≫ Mzk1G1PsiGlueCompatActual.psi n T)
      = Mzk1G1PsiGlobalActual.psiChart0 n T := Mzk1G1PsiGlueCompatActual.psi_ι_false n T
  rw [h1]
  have h2 : Mzk1G1PsiGlobalActual.psiChart0 n T
      = (Spec.map (CommRingCat.ofHom (evalAt (R := R n) (psiChart0Coord n T)))) ≫
        localChartInf := rfl
  rw [h2, Category.assoc]
  congr 1
  have h3 : localChartInf ≫ hPoly h hh = hPolyChartOf h HIdx.c0 := by
    have h4 : (hPolyCover h hh).f HIdx.c0 ≫ hPoly h hh = hPolyChartOf h HIdx.c0 :=
      hPoly_ι_c0 h hh
    rwa [hPolyCover_f] at h4
  rw [h3]
  rfl

/-- Point-level form of `phi_chart0_eq`. -/
theorem phi_chart0_apply (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (x : fermatChart0Scheme n) :
    Mzk1G1PsiB1Actual.phi n T h hh ((fermatChart0ToCurve n).base x)
      = localChartInf.base (PrimeSpectrum.comap (evalAt (R := Polynomial ℚ) h)
          (PrimeSpectrum.comap (evalAt (R := R n) (psiChart0Coord n T)) x)) := by
  have hx := congrArg (fun g : fermatChart0Scheme n ⟶ projectiveLineGlued => g.base x)
    (phi_chart0_eq n T h hh)
  simpa only [Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom] using hx

/-- **Chart 0 fibre bound**: over the `t`-chart point of coordinate `c`, the fibre on the
first chart of `Y_n` is contained in the zero set of `(h - C c) (psiChart0Coord)`. -/
theorem chart0_fibre_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (c : ℚ) (y : PrimeSpectrum (Polynomial ℚ))
    (hy : Polynomial.X - Polynomial.C c ∈ y.asIdeal) :
    {x : fermatChart0Scheme n |
        Mzk1G1PsiB1Actual.phi n T h hh ((fermatChart0ToCurve n).base x) = localChartInf.base y}
      ⊆ {x : fermatChart0Scheme n | gHom n T (h - Polynomial.C c) ∈ x.asIdeal} := by
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [phi_chart0_apply] at hx
  have hinj : Function.Injective localChartInf := localChartInf.isOpenEmbedding.injective
  have hEq : PrimeSpectrum.comap (evalAt (R := Polynomial ℚ) h)
      (PrimeSpectrum.comap (evalAt (R := R n) (psiChart0Coord n T)) x) = y := hinj hx
  have h1 : Polynomial.X - Polynomial.C c ∈
      (PrimeSpectrum.comap (evalAt (R := Polynomial ℚ) h)
        (PrimeSpectrum.comap (evalAt (R := R n) (psiChart0Coord n T)) x)).asIdeal := by
    rw [hEq]
    exact hy
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
  rw [evalAt_poly] at h1
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
  rwa [evalAt_gHom_eq] at h1

/-! ## 4. The second chart of the curve -/

/-- The range of the Fermat overlap inside the second chart is the principal open `D(r)`. -/
theorem range_overlapToChartInf_eq (n : Nat) :
    Set.range (Mzk1G1FermatOverlapActual.overlapToChartInf n)
      = (PrimeSpectrum.basicOpen (Mzk1G1FermatOverlapActual.r1 n) :
          Set (PrimeSpectrum (R2 n))) := by
  have hdef : Mzk1G1FermatOverlapActual.overlapToChartInf n
      = (Mzk1G1FermatOverlapActual.overlapSchemeIso n).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (R2 n) (Mzk1G1FermatOverlapActual.OverlapInf n))) := rfl
  rw [hdef]
  have hrange : Set.range ((Mzk1G1FermatOverlapActual.overlapSchemeIso n).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (R2 n) (Mzk1G1FermatOverlapActual.OverlapInf n))))
      = Set.range (Spec.map (CommRingCat.ofHom
        (algebraMap (R2 n) (Mzk1G1FermatOverlapActual.OverlapInf n)))) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(Mzk1G1FermatOverlapActual.overlapSchemeIso n).hom w, rfl⟩
    · rintro ⟨w, rfl⟩
      refine ⟨(Mzk1G1FermatOverlapActual.overlapSchemeIso n).inv w, ?_⟩
      have hv : (Mzk1G1FermatOverlapActual.overlapSchemeIso n).hom
          ((Mzk1G1FermatOverlapActual.overlapSchemeIso n).inv w) = w := by
        have hv' := congrArg (fun g => g w)
          (Mzk1G1FermatOverlapActual.overlapSchemeIso n).inv_hom_id
        simpa using hv'
      rw [Scheme.Hom.comp_apply, hv]
  rw [hrange]
  exact range_algebraMap_away (R := CommRingCat.of (R2 n))
    (Mzk1G1FermatOverlapActual.r1 n)

/-- **A point of the second chart with `r ≠ 0` is a point of the first chart.** -/
theorem qPiece_mem_range_chart0 (n : Nat) (T : Finset ℚ)
    (P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)))
    (hP : algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))
      (Mzk1G1FermatOverlapActual.r1 n) ∉ P.asIdeal) :
    (qPiece n T).base P ∈ Set.range (fermatChart0ToCurve n) := by
  set z : PrimeSpectrum (R2 n) :=
    PrimeSpectrum.comap (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))) P
    with hzdef
  have hzp : (qPiece n T).base P = (fermatChartInfToCurve n).base z := by
    rw [qPiece, Scheme.Hom.comp_apply, hzdef]
    congr 1
  rw [hzp]
  have hz : Mzk1G1FermatOverlapActual.r1 n ∉ z.asIdeal := by
    rw [hzdef, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    exact hP
  have hmem : z ∈ Set.range (Mzk1G1FermatOverlapActual.overlapToChartInf n) := by
    rw [range_overlapToChartInf_eq]
    exact (PrimeSpectrum.mem_basicOpen (Mzk1G1FermatOverlapActual.r1 n) z).mpr hz
  obtain ⟨w, hw⟩ := hmem
  refine ⟨Mzk1G1FermatOverlapActual.overlapToChart0 n w, ?_⟩
  rw [← hw]
  have hcond := Mzk1G1PsiGlobalActual.overlapToCurve_condition n
  have hw' := congrArg (fun g => g w) hcond
  simpa only [Scheme.Hom.comp_apply] using hw'

/-- **The fibre is covered by the first chart and the `r = 0` locus of the second chart.** -/
theorem fibre_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (q : projectiveLineGlued) :
    (Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {q} ⊆
      (fermatChart0ToCurve n).base '' ((fermatChart0ToCurve n).base ⁻¹'
        ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {q}))
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
          (Mzk1G1FermatOverlapActual.r1 n) ∉ P.asIdeal := by
        rwa [show Mzk1G1FermatOverlapActual.r1 n = chartR n from rfl]
      obtain ⟨x, hx⟩ := qPiece_mem_range_chart0 n T P hP'
      refine ⟨x, ?_, hx⟩
      show (Mzk1G1PsiB1Actual.phi n T h hh).base ((fermatChart0ToCurve n).base x) = q
      rw [hx]
      exact hz

/-! ## 5. The scheme-level fibre finiteness theorems -/

/-- **Scheme-level fibre finiteness at the `t`-chart points of rational coordinate.** -/
theorem phi_fiber_finite_of_chartInf (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (hT : T.Nonempty) (h0 : (0 : ℚ) ∉ T)
    (hdeg : 0 < h.natDegree) (c : ℚ) (y : PrimeSpectrum (Polynomial ℚ))
    (hy : Polynomial.X - Polynomial.C c ∈ y.asIdeal) :
    ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {localChartInf.base y}).Finite := by
  classical
  have hS0 : {x : fermatChart0Scheme n | gHom n T (h - Polynomial.C c) ∈ x.asIdeal}.Finite :=
    finite_primes_of_gHom_poly n T hT (h - Polynomial.C c) (sub_C_ne_zero hdeg c)
  have hS1 : {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
      algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
        P.asIdeal}.Finite :=
    finite_primes_chartR n T hn
  have hpre0 : (fermatChart0ToCurve n).base ⁻¹'
      ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {localChartInf.base y})
      ⊆ {x : fermatChart0Scheme n | gHom n T (h - Polynomial.C c) ∈ x.asIdeal} :=
    chart0_fibre_subset n T h hh c y hy
  have hU : (((fermatChart0ToCurve n).base '' {x : fermatChart0Scheme n |
        gHom n T (h - Polynomial.C c) ∈ x.asIdeal})
      ∪ ((qPiece n T).base '' {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
          algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
            P.asIdeal})).Finite :=
    (hS0.image (fermatChart0ToCurve n).base).union (hS1.image (qPiece n T).base)
  refine hU.subset ?_
  intro z hz
  rcases fibre_subset n T h hh (localChartInf.base y) hz with h1 | h1
  · exact Or.inl (Set.image_mono hpre0 h1)
  · exact Or.inr h1

/-- **Scheme-level fibre finiteness outside the `t`-chart** (in particular at `λ = 0`). -/
theorem phi_fiber_finite_of_notMem (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (hT : T.Nonempty) (h0 : (0 : ℚ) ∉ T)
    (q : projectiveLineGlued) (hq : q ∉ Set.range localChartInf) :
    ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {q}).Finite := by
  classical
  have hS1 : {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
      algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
        P.asIdeal}.Finite :=
    finite_primes_chartR n T hn
  have hempty : (fermatChart0ToCurve n).base ⁻¹'
      ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {q}) = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    rw [phi_chart0_apply] at hx
    exact hq ⟨_, hx⟩
  have hfin0 : ((fermatChart0ToCurve n).base '' ((fermatChart0ToCurve n).base ⁻¹'
      ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {q}))).Finite := by
    rw [hempty, Set.image_empty]
    exact Set.finite_empty
  have hU : (((fermatChart0ToCurve n).base '' ((fermatChart0ToCurve n).base ⁻¹'
        ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {q})))
      ∪ ((qPiece n T).base '' {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
          algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
            P.asIdeal})).Finite :=
    hfin0.union (hS1.image (qPiece n T).base)
  refine hU.subset ?_
  intro z hz
  rcases fibre_subset n T h hh q hz with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

/-- **MAIN THEOREM (adapted statement).** The fibre of `phi n T h hh` over a point `q` is finite,
provided `h` is nonconstant and `q` is either outside the `t`-chart of `P^1` or the
closed point of the `t`-chart with a rational coordinate.  (The unrestricted form over all
`q` is false for constant `h`; see the file header.) -/
theorem phi_fiber_finite (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (hn : 0 < n) (hT : T.Nonempty) (h0 : (0 : ℚ) ∉ T) (hdeg : 0 < h.natDegree)
    (q : projectiveLineGlued)
    (hq : q ∉ Set.range localChartInf ∨
      ∃ (c : ℚ) (y : PrimeSpectrum (Polynomial ℚ)),
        Polynomial.X - Polynomial.C c ∈ y.asIdeal ∧ q = localChartInf.base y) :
    ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {q}).Finite := by
  rcases hq with hq | ⟨c, y, hy, rfl⟩
  · exact phi_fiber_finite_of_notMem n T h hh hn hT h0 q hq
  · exact phi_fiber_finite_of_chartInf n T h hh hn hT h0 hdeg c y hy

/-! ## 6. The boundary points `{0, 1, ∞}` -/

/-- The closed point of the affine chart `ℚ[s]` with coordinate `c`. -/
noncomputable def chartPrime (c : ℚ) : PrimeSpectrum (Polynomial ℚ) :=
  ⟨Ideal.span ({Polynomial.X - Polynomial.C c} : Set (Polynomial ℚ)), isPrime_span_X_sub_C c⟩

theorem chartPrime_mem (c : ℚ) :
    Polynomial.X - Polynomial.C c ∈ (chartPrime c).asIdeal :=
  Ideal.subset_span (Set.mem_singleton _)

/-- Any prime containing `X - C c` is that maximal ideal (the quotient is `ℚ`). -/
theorem chartPrime_eq_of_mem (c : ℚ) (p : PrimeSpectrum (Polynomial ℚ))
    (hp : Polynomial.X - Polynomial.C c ∈ p.asIdeal) : p = chartPrime c := by
  haveI hfield : IsField (Polynomial ℚ ⧸
      Ideal.span ({Polynomial.X - Polynomial.C c} : Set (Polynomial ℚ))) :=
    (Polynomial.quotientSpanXSubCAlgEquiv c).toRingEquiv.isField (Field.toIsField ℚ)
  haveI hmax : (Ideal.span ({Polynomial.X - Polynomial.C c} : Set (Polynomial ℚ))).IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hfield
  have hle : Ideal.span ({Polynomial.X - Polynomial.C c} : Set (Polynomial ℚ)) ≤ p.asIdeal :=
    Ideal.span_le.mpr (by simpa using hp)
  have heq : Ideal.span ({Polynomial.X - Polynomial.C c} : Set (Polynomial ℚ)) = p.asIdeal :=
    hmax.eq_of_le p.isPrime.ne_top hle
  exact PrimeSpectrum.ext heq.symm

/-- The range of the `λ`-chart inclusion is the principal open `D(X)`. -/
theorem range_overlapToChart0_eq :
    Set.range (overlapToChart0) = (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) :
      Set (PrimeSpectrum (Polynomial ℚ))) := by
  have hbridge : ∀ x, overlapToChart0 x
      = PrimeSpectrum.comap (algebraMap (Polynomial ℚ) OverlapRing) x := by
    intro x
    show (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) OverlapRing))).base x
      = PrimeSpectrum.comap (algebraMap (Polynomial ℚ) OverlapRing) x
    simp only [Spec.map_apply, CommRingCat.hom_ofHom]
  have hrange : Set.range (overlapToChart0)
      = Set.range (PrimeSpectrum.comap (algebraMap (Polynomial ℚ) OverlapRing)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, hbridge x⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, (hbridge x).symm⟩
  rw [hrange]
  exact PrimeSpectrum.localization_away_comap_range (S := OverlapRing) (Polynomial.X : Polynomial ℚ)

/-- **The `t`-chart point of coordinate `1` is also the `λ`-chart point of coordinate `1`**
(the overlap bridge; `1⁻¹ = 1`). -/
theorem exists_chartInf_of_chart0 (p : PrimeSpectrum (Polynomial ℚ))
    (hp : Polynomial.X - Polynomial.C 1 ∈ p.asIdeal) :
    ∃ y : PrimeSpectrum (Polynomial ℚ), Polynomial.X - Polynomial.C 1 ∈ y.asIdeal ∧
      localChart0.base p = localChartInf.base y := by
  have hpX : Polynomial.X ∉ p.asIdeal := by
    intro hX
    have hsub : Polynomial.X - (Polynomial.X - Polynomial.C (1 : ℚ)) ∈ p.asIdeal :=
      Ideal.sub_mem _ hX hp
    have heq : Polynomial.X - (Polynomial.X - Polynomial.C (1 : ℚ)) = (1 : Polynomial ℚ) := by
      rw [Polynomial.C_1]
      ring
    rw [heq] at hsub
    exact p.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr hsub)
  have hpb : p ∈ Set.range (overlapToChart0) := by
    rw [range_overlapToChart0_eq]
    exact (PrimeSpectrum.mem_basicOpen (Polynomial.X : Polynomial ℚ) p).mpr hpX
  obtain ⟨w, hw⟩ := hpb
  refine ⟨PrimeSpectrum.comap (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) w,
    ?_, ?_⟩
  · rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hw' : PrimeSpectrum.comap (algebraMap (Polynomial ℚ) OverlapRing) w = p := hw
    have halg : algebraMap (Polynomial ℚ) OverlapRing (Polynomial.X - Polynomial.C (1 : ℚ)) ∈
        w.asIdeal := by
      have h1 : Polynomial.X - Polynomial.C (1 : ℚ) ∈
          (PrimeSpectrum.comap (algebraMap (Polynomial ℚ) OverlapRing) w).asIdeal := by
        rw [hw']
        exact hp
      rwa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    have halgX : algebraMap (Polynomial ℚ) OverlapRing (Polynomial.X - Polynomial.C (1 : ℚ))
        = ovLambda - 1 := by
      rw [map_sub, Polynomial.C_1, map_one]
      rfl
    have hconv : (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing))
        (Polynomial.X - Polynomial.C (1 : ℚ)) = invLambda - 1 := by
      rw [RingHom.comp_apply, halgX, map_sub, invAuto_ovLambda, map_one]
    rw [hconv]
    have hident : (algebraMap (Polynomial ℚ) OverlapRing (Polynomial.X - Polynomial.C (1 : ℚ))) *
        (-invLambda) = invLambda - 1 := by
      rw [halgX, sub_mul, mul_neg, ovLambda_mul_invLambda, one_mul]
      ring
    rw [← hident]
    exact Ideal.mul_mem_right _ _ halg
  · calc localChart0.base p = localChart0.base (overlapToChart0.base w) := by rw [hw]
      _ = (overlapToChart0 ≫ localChart0).base w := by rw [Scheme.Hom.comp_apply]
      _ = (overlapToChartInf ≫ localChartInf).base w := by rw [localChart_overlap_condition]
      _ = localChartInf.base (overlapToChartInf.base w) := by rw [Scheme.Hom.comp_apply]
      _ = localChartInf.base (PrimeSpectrum.comap
            (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) w) := by
          rw [show overlapToChartInf
            = Spec.map (CommRingCat.ofHom (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)))
            from rfl]
          simp only [Spec.map_apply, CommRingCat.hom_ofHom]

/-- The `λ = 0` point of `P^1` is not in the `t`-chart. -/
theorem localChart0_chartPrime_zero_notMem :
    localChart0.base (chartPrime 0) ∉ Set.range localChartInf := by
  intro hmem
  have h1 : localChart0.base (chartPrime 0) ∈ localChartInf.opensRange :=
    (Scheme.Hom.mem_opensRange (f := localChartInf)).mpr hmem
  have h2 : chartPrime 0 ∈ localChart0 ⁻¹ᵁ localChartInf.opensRange :=
    (Scheme.Hom.mem_preimage (f := localChart0) (U := localChartInf.opensRange)).mpr h1
  rw [localChart0_preimage_localChartInf] at h2
  have h4 : chartPrime 0 ∈ Set.range (overlapToChart0) :=
    (Scheme.Hom.mem_opensRange (f := overlapToChart0)).mp h2
  rw [range_overlapToChart0_eq] at h4
  have hX : Polynomial.X ∈ (chartPrime 0).asIdeal := by
    have hmemX : Polynomial.X - Polynomial.C (0 : ℚ) ∈ (chartPrime 0).asIdeal := chartPrime_mem 0
    simpa using hmemX
  exact (PrimeSpectrum.mem_basicOpen (Polynomial.X : Polynomial ℚ) (chartPrime 0)).mp h4 hX

/-- The fibre of `phi` over `λ = 0` is finite. -/
theorem phi_fiber_finite_p1Zero (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (hn : 0 < n) (hT : T.Nonempty) (h0 : (0 : ℚ) ∉ T) (hdeg : 0 < h.natDegree) :
    ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' p1Zero).Finite := by
  have hsub : p1Zero ⊆ {localChart0.base (chartPrime 0)} := by
    intro z hz
    rw [p1Zero] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    simp only [chartPoint, Set.mem_setOf_eq] at hp
    rw [chartPrime_eq_of_mem 0 p hp]
    exact Set.mem_singleton _
  refine (phi_fiber_finite_of_notMem n T h hh hn hT h0 _
    localChart0_chartPrime_zero_notMem).subset ?_
  exact Set.preimage_mono hsub

/-- The fibre of `phi` over `λ = 1` is finite. -/
theorem phi_fiber_finite_p1One (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (hn : 0 < n) (hT : T.Nonempty) (h0 : (0 : ℚ) ∉ T) (hdeg : 0 < h.natDegree) :
    ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' p1One).Finite := by
  have hsub : p1One ⊆ {localChart0.base (chartPrime 1)} := by
    intro z hz
    rw [p1One] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    simp only [chartPoint, Set.mem_setOf_eq] at hp
    rw [chartPrime_eq_of_mem 1 p hp]
    exact Set.mem_singleton _
  have hpre : (Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' p1One ⊆
      (Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' {localChart0.base (chartPrime 1)} :=
    Set.preimage_mono hsub
  obtain ⟨y, hy, hq⟩ := exists_chartInf_of_chart0 (chartPrime 1) (chartPrime_mem 1)
  rw [hq] at hpre
  exact (phi_fiber_finite_of_chartInf n T h hh hn hT h0 hdeg 1 y hy).subset hpre

/-- The fibre of `phi` over `t = 0` (the point at infinity) is finite. -/
theorem phi_fiber_finite_p1Infinity (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (hn : 0 < n) (hT : T.Nonempty) (h0 : (0 : ℚ) ∉ T) (hdeg : 0 < h.natDegree) :
    ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' p1Infinity).Finite := by
  have hsub : p1Infinity ⊆ {localChartInf.base (chartPrime 0)} := by
    intro z hz
    rw [p1Infinity] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    simp only [chartPoint, Set.mem_setOf_eq] at hp
    rw [chartPrime_eq_of_mem 0 p hp]
    exact Set.mem_singleton _
  refine (phi_fiber_finite_of_chartInf n T h hh hn hT h0 hdeg 0 (chartPrime 0)
    (chartPrime_mem 0)).subset ?_
  exact Set.preimage_mono hsub

/-- **CONSUMER FORM (B1FiniteProducer / item A).** The full boundary preimage
`phi.base ⁻¹' {0, 1, ∞}` is finite. -/
theorem phi_boundaryPreimage_finite (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (hn : 0 < n) (hT : T.Nonempty) (h0 : (0 : ℚ) ∉ T) (hdeg : 0 < h.natDegree) :
    ((Mzk1G1PsiB1Actual.phi n T h hh).base ⁻¹' boundarySetGlued).Finite :=
  Mzk1G1PsiB1Actual.boundaryPreimage_finite_of_each n (Mzk1G1PsiB1Actual.phi n T h hh)
    (phi_fiber_finite_p1Zero n T h hh hn hT h0 hdeg)
    (phi_fiber_finite_p1One n T h hh hn hT h0 hdeg)
    (phi_fiber_finite_p1Infinity n T h hh hn hT h0 hdeg)

/-! ## Axiom checks -/
#print axioms finite_primes_of_gHom_poly
#print axioms finite_primes_of_rHom_poly
#print axioms finite_primes_of_rHom_localized
#print axioms finite_primes_chartR
#print axioms sub_C_ne_zero
#print axioms evalAt_poly
#print axioms evalAt_gHom_eq
#print axioms phi_chart0_eq
#print axioms phi_chart0_apply
#print axioms chart0_fibre_subset
#print axioms range_overlapToChartInf_eq
#print axioms qPiece_mem_range_chart0
#print axioms fibre_subset
#print axioms phi_fiber_finite_of_chartInf
#print axioms phi_fiber_finite_of_notMem
#print axioms phi_fiber_finite
#print axioms chartPrime
#print axioms chartPrime_mem
#print axioms chartPrime_eq_of_mem
#print axioms exists_chartInf_of_chart0
#print axioms localChart0_chartPrime_zero_notMem
#print axioms phi_fiber_finite_p1Zero
#print axioms phi_fiber_finite_p1One
#print axioms phi_fiber_finite_p1Infinity
#print axioms phi_boundaryPreimage_finite

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFiberFiniteActual
