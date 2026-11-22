/-
# B1 / O3b: the out-of-chart piece `hout` of the O3(ii)(b) reduction

Consumer: `Mzk1G1B1HPolySmoothLocusActual.hpts_union_p1Zero_of_hbridge_and_out` /
`hbH_of_hbridge_and_out` (and hence `Mzk1G1B1HbObligationsActual` and the B1 branch lane
`Mzk1G1PhiFixedLBranchSupportActual`).

## Goal

```
hout :  hPoly h hh '' (Ram (hPoly h hh) \ Set.range localChartInf.base) ⊆
          chartMorphismInf h '' derivativeZeroSet h ∪ p1Zero
```

The statement is literally the one of
`Mzk1G1B1HPolySmoothLocusActual.hbH_of_hbridge_and_out`; as there, `Ram (hPoly h hh)`
needs the local-finite-presentation instance of `hPoly h hh` (it is an instance argument
of `Ram`), so `hout` carries it too (every consumer already supplies it).

## Mathematics

`localChartInf` is the `t`-chart of the glued projective line, with transition
`t = 1 / λ` on the overlap.  The `t`-chart omits exactly the point `t = ∞`, i.e. the
`λ`-chart point `λ = 0`, which is `p1Zero = localChart0 '' {X = 0}`.  Hence the set
difference in `hout` is contained in the single point `p1Zero`:

1. `compl_range_localChartInf_subset_p1Zero` (and the reverse inclusion
   `p1Zero_subset_compl_range_localChartInf`, so `(range localChartInf)ᶜ = p1Zero`):
   cover `P¹` by the two charts (`localChart_jointly_surjective`); a point outside the
   `t`-chart is `localChart0 p`, and `p` is not in the overlap
   (`localChart0_preimage_localChartInf`), so the `λ`-coordinate `X` lies in `p`
   (`PrimeSpectrum.mem_basicOpen`, `range_overlapToChart0_coe`).

2. `hPoly_image_p1Zero_subset`: `hPoly h hh '' p1Zero ⊆ p1Zero`.  On the piece
   `c2 = D(hRev)` of the cover of `hPoly` (chart map `chartMorphism0 (hPolyLam h)`,
   donor `hPoly_ι_c2`) the point `λ = 0` is an `X`-torsion point:
   `hRev h` has constant coefficient `h.leadingCoeff ≠ 0` (donor
   `Mzk1G1PsiFiberFiniteC2Actual.hRev_coeff_zero`), so `hRev h ∉ p` for `X ∈ p`
   (otherwise `C h.leadingCoeff` — which differs from `hRev h` by a multiple of `X`
   (`Polynomial.X_dvd_sub_C`) — would be a unit in `p`, forcing `p = ⊤`).
   Thus `p` lifts to the `D(hRev)` piece, where
   `hPolyLam h = X ^ d * (hRev h)⁻¹` contains `X ^ d` and grace's
   `hPolyLam_mem_iff` (for `d > 0`) gives `hPolyLam h ∈ q ↔ algebraMap X ∈ q`,
   so the image is `p1Zero` by `chartMorphism0_mem_p1Zero_iff`.

3. `hout` follows: a ramification point outside the `t`-chart is `p1Zero` by 1,
   and its value is `p1Zero` by 2.

## Explicit obligations

None: every declaration below is closed.  No `sorry`, no `admit`, no new axiom.
-/
import tmp.sheaf.xif.paper.Mzk1G1B1HPolyLamZeroActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyFinalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFiberFiniteC2Actual
import tmp.sheaf.xif.paper.Mzk1G1B1HPolyBranchSchemeActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1HoutActual

open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyLamZeroActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyBranchSchemeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberFiniteC2Actual

/-! ## 1. The complement of the `t`-chart is the point `p1Zero` -/

/-- The open range of the overlap inclusion into the `λ`-chart is the principal open
`D(X)`: the overlap is `Spec ℚ[X, X⁻¹]` inside `Spec ℚ[X]`. -/
theorem range_overlapToChart0_coe :
    Set.range overlapToChart0 =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) :
        Set (PrimeSpectrum (Polynomial ℚ))) := by
  rw [← opensRange_coe_eq_range (f := overlapToChart0)]
  exact range_algebraMap_away (R := CommRingCat.of (Polynomial ℚ)) (Polynomial.X)

/-- A prime of `ℚ[λ]` lies in the range of the overlap inclusion `D(X) ⊂ Spec ℚ[λ]`
exactly when `X` is not in it, i.e. exactly when the `λ`-coordinate of the point is
invertible. -/
theorem mem_range_overlapToChart0_iff (p : PrimeSpectrum (Polynomial ℚ)) :
    p ∈ Set.range overlapToChart0 ↔ Polynomial.X ∉ p.asIdeal := by
  rw [range_overlapToChart0_coe]
  exact PrimeSpectrum.mem_basicOpen (Polynomial.X) p

/-- Membership in the chart point `λ = 0`: a prime contains `X - C 0` exactly when it
contains `X`. -/
theorem mem_chartPoint_zero_iff (p : PrimeSpectrum (Polynomial ℚ)) :
    p ∈ chartPoint 0 ↔ Polynomial.X ∈ p.asIdeal := by
  show Polynomial.X - Polynomial.C (0 : ℚ) ∈ p.asIdeal ↔ Polynomial.X ∈ p.asIdeal
  simp

/-- **The `λ = 0` point is not in the `t`-chart** (`t = ∞`). -/
theorem p1Zero_subset_compl_range_localChartInf (x : projectiveLineGlued)
    (hx : x ∈ p1Zero) : x ∉ Set.range localChartInf.base := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hX : Polynomial.X ∈ p.asIdeal := (mem_chartPoint_zero_iff p).mp hp
  intro hmem
  have h1 : localChart0.base p ∈ localChartInf.opensRange := hmem
  have h2 : p ∈ localChart0 ⁻¹ᵁ localChartInf.opensRange :=
    (Scheme.Hom.mem_preimage (f := localChart0) (U := localChartInf.opensRange)).mpr h1
  rw [localChart0_preimage_localChartInf] at h2
  have h3 : p ∈ (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) :
      Set (PrimeSpectrum (Polynomial ℚ))) := by
    rw [← range_overlapToChart0_coe]
    exact h2
  exact ((PrimeSpectrum.mem_basicOpen (Polynomial.X) p).mp h3) hX

/-- **Every point outside the `t`-chart is the `λ = 0` point** `p1Zero`.
The two charts cover `P¹`, so such a point is `localChart0 p`; it is not in the overlap,
so `X ∈ p` and `localChart0 p` is a point of `p1Zero = localChart0 '' {X = 0}`. -/
theorem compl_range_localChartInf_subset_p1Zero (x : projectiveLineGlued)
    (hx : x ∉ Set.range localChartInf.base) : x ∈ p1Zero := by
  rcases localChart_jointly_surjective x with hx0 | hxi
  · obtain ⟨p, rfl⟩ := hx0
    have hnot : p ∉ overlapToChart0.opensRange := by
      intro hp
      rw [← localChart0_preimage_localChartInf] at hp
      have h1 : localChart0.base p ∈ localChartInf.opensRange :=
        (Scheme.Hom.mem_preimage (f := localChart0) (U := localChartInf.opensRange)).mp hp
      exact hx h1
    have hX : Polynomial.X ∈ p.asIdeal := by
      by_contra hX
      have hb : p ∈ (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) :
          Set (PrimeSpectrum (Polynomial ℚ))) :=
        (PrimeSpectrum.mem_basicOpen (Polynomial.X) p).mpr hX
      rw [← range_overlapToChart0_coe] at hb
      exact hnot hb
    exact ⟨p, (mem_chartPoint_zero_iff p).mpr hX, rfl⟩
  · exact absurd hxi hx

/-- **The complement of the `t`-chart is exactly the point `p1Zero`** (the
`λ = 0`, `t = ∞` point): the honest form of `range localChartInf = P¹ ∖ {p1Zero}`. -/
theorem compl_range_localChartInf_eq_p1Zero :
    (Set.range localChartInf.base)ᶜ = p1Zero :=
  Set.ext fun x => ⟨fun hx => compl_range_localChartInf_subset_p1Zero x hx,
    fun hx => p1Zero_subset_compl_range_localChartInf x hx⟩

/-! ## 2. `hPoly` fixes the point `p1Zero` -/

/-- **`hRev h` does not vanish at the `λ = 0` point**: for a prime `X ∈ p` of
`ℚ[λ]`, `hRev h ∉ p`.  Otherwise `C h.leadingCoeff` — which differs from
`hRev h` by a multiple of `X` (`Polynomial.X_dvd_sub_C` + `hRev_coeff_zero`) — would
lie in `p` as a unit, forcing `p = ⊤`. -/
theorem hRev_not_mem_of_X_mem (h : Polynomial ℚ) (hh : h ≠ 0)
    (p : PrimeSpectrum (Polynomial ℚ)) (hX : Polynomial.X ∈ p.asIdeal) :
    hRev h ∉ p.asIdeal := by
  intro hmem
  have hdvd : Polynomial.X ∣ hRev h - Polynomial.C ((hRev h).coeff 0) :=
    Polynomial.X_dvd_sub_C (p := hRev h)
  have hcoeff : (hRev h).coeff 0 = h.leadingCoeff := hRev_coeff_zero h hh
  have hsub : hRev h - Polynomial.C ((hRev h).coeff 0) ∈ p.asIdeal := by
    obtain ⟨G, hG⟩ := hdvd
    rw [hG, mul_comm]
    exact Ideal.mul_mem_left p.asIdeal G hX
  have hC : Polynomial.C h.leadingCoeff ∈ p.asIdeal := by
    have h' : hRev h - (hRev h - Polynomial.C ((hRev h).coeff 0)) ∈ p.asIdeal :=
      Ideal.sub_mem _ hmem hsub
    rwa [sub_sub_cancel, hcoeff] at h'
  have hunit : IsUnit (Polynomial.C h.leadingCoeff) := by
    rw [Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hh)
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem (I := p.asIdeal) hC hunit)

/-- **`hPoly` sends the point `p1Zero` to `p1Zero`** (task declaration 2).

At the `λ = 0` point the cover piece `c2 = D(hRev)` (chart map
`chartMorphism0 (hPolyLam h)`, donor `hPoly_ι_c2`) applies: `hRev h` is invertible
there, and `hPolyLam h = X ^ d * (hRev h)⁻¹` contains `X ^ d` hence `X`; by
`hPolyLam_mem_iff` (`d > 0`) this is exactly `algebraMap X ∈ q`, i.e. the image is
the `λ = 0` point (`chartMorphism0_mem_p1Zero_iff`). -/
theorem hPoly_image_p1Zero_subset (h : Polynomial ℚ) (hh : h ≠ 0) (hdeg : 0 < h.natDegree) :
    hPoly h hh '' p1Zero ⊆ p1Zero := by
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨p, hp, rfl⟩ := hz
  have hX : Polynomial.X ∈ p.asIdeal := (mem_chartPoint_zero_iff p).mp hp
  have hRevnot : hRev h ∉ p.asIdeal := hRev_not_mem_of_X_mem h hh p hX
  have hrange : p ∈ Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial ℚ) (Localization.Away (hRev h))))) := by
    rw [range_algebraMap_away (R := CommRingCat.of (Polynomial ℚ)) (hRev h)]
    exact (PrimeSpectrum.mem_basicOpen (hRev h) p).mpr hRevnot
  obtain ⟨y, hy⟩ := hrange
  have hz2 : localChart0.base p = (hPolyCover h hh).f HIdx.c2 y := by
    show localChart0.base p = (hPolyPieceMap h HIdx.c2) y
    rw [show hPolyPieceMap h HIdx.c2 =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)))) ≫
        localChart0 from rfl]
    rw [Scheme.Hom.comp_apply, hy]
  rw [hz2]
  rw [← Scheme.Hom.comp_apply, hPoly_ι_c2 h hh]
  show chartMorphism0 (R := Localization.Away (hRev h)) (hPolyLam h) y ∈ p1Zero
  rw [chartMorphism0_mem_p1Zero_iff, hPolyLam_mem_iff h hdeg]
  have hmem : Polynomial.X ∈ ((Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial ℚ) (Localization.Away (hRev h))))) y).asIdeal := by
    rw [hy]
    exact hX
  rw [Spec.map_apply, CommRingCat.hom_ofHom, PrimeSpectrum.comap_asIdeal] at hmem
  exact (Ideal.mem_comap).mp hmem

/-! ## 3. `hout` -/

/-- **`hout` — the out-of-chart piece of the O3(ii)(b) reduction is closed** (task
declaration 1).  A ramification point outside the `t`-chart is the point `p1Zero`
(`compl_range_localChartInf_subset_p1Zero`), whose image under `hPoly` is again
`p1Zero` (`hPoly_image_p1Zero_subset`).  The target of the inclusion is the one of
`hbH_of_hbridge_and_out`, so the out-of-chart piece is discharged there. -/
theorem hout (h : Polynomial ℚ) (hh : h ≠ 0) (hdeg : 0 < h.natDegree)
    [LocallyOfFinitePresentation (hPoly h hh)] :
    hPoly h hh '' (Ram (hPoly h hh) \ Set.range localChartInf.base) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h ∪ p1Zero := by
  rintro y ⟨z, ⟨-, hzout⟩, rfl⟩
  exact Or.inr (hPoly_image_p1Zero_subset h hh hdeg
    ⟨z, compl_range_localChartInf_subset_p1Zero z hzout, rfl⟩)

/-! ## Axiom checks -/

#print axioms range_overlapToChart0_coe
#print axioms mem_range_overlapToChart0_iff
#print axioms mem_chartPoint_zero_iff
#print axioms p1Zero_subset_compl_range_localChartInf
#print axioms compl_range_localChartInf_subset_p1Zero
#print axioms compl_range_localChartInf_eq_p1Zero
#print axioms hRev_not_mem_of_X_mem
#print axioms hPoly_image_p1Zero_subset
#print axioms hout

end LeanFormal.IUT.XiFPaper.Mzk1G1B1HoutActual
