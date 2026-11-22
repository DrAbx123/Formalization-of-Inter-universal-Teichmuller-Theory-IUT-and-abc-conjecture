import tmp.sheaf.xif.paper.S2853ChartYNegationActual
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import Mathlib.AlgebraicGeometry.Cover.Directed

noncomputable section
open LeanFormal.IUT CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual

variable (K : Type) [Field K]

abbrev tY : E37ChartYRing K := S2853ChartYT K
abbrev sY : E37ChartYRing K := S2853ChartYS K

abbrev V0 : Scheme := Spec (CommRingCat.of (S2853ChartYNegRing K))

abbrev g0Vals : Fin 2 → S2853ChartYNegRing K := S2853G0Vals K

abbrev g0Poly : MvPolynomial (Fin 2) K →+* S2853ChartYNegRing K := S2853G0Poly K

theorem g0Poly_relation :
    g0Poly K (E37ChartYPolynomial K) = 0 := by
  change S2853G0Poly K (E37ChartYPolynomial K) = 0
  exact S2853G0Poly_relation K

abbrev V1 : Scheme := Spec (CommRingCat.of (Localization.Away (tY K)))

noncomputable def g1Unit : (Localization.Away (tY K))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (x := tY K) (S := Localization.Away (tY K))).unit

/-- Chart-Z coordinates on D(t): x = s/t, y = -1 - 1/t. -/
noncomputable def g1Vals : Fin 2 → Localization.Away (tY K)
  | ⟨0, _⟩ => algebraMap (E37ChartYRing K) (Localization.Away (tY K)) (sY K) *
      ↑((g1Unit K)⁻¹)
  | ⟨1, _⟩ => -1 - ↑((g1Unit K)⁻¹)
  | ⟨n + 2, h⟩ => absurd h (by omega)

noncomputable def g1Poly :
    MvPolynomial (Fin 2) K →+* Localization.Away (tY K) :=
  MvPolynomial.eval₂Hom (algebraMap K _) (g1Vals K)

theorem g1_hrel :
    algebraMap (E37ChartYRing K) (Localization.Away (tY K))
      ((sY K)^3 - sY K * (tY K)^2 - tY K - (tY K)^2) = 0 := by
  have h : (sY K)^3 - sY K * (tY K)^2 - tY K - (tY K)^2 = 0 := by
    simpa [sY, tY, E37ChartYPolynomial] using chartYRelation_quotient K
  rw [h, map_zero]

theorem g1Poly_scale :
    (↑(g1Unit K) : Localization.Away (tY K))^3 *
      g1Poly K (S2801E37Polynomial K) =
      -algebraMap (E37ChartYRing K) (Localization.Away (tY K))
        ((sY K)^3 - sY K * (tY K)^2 - tY K - (tY K)^2) := by
  let W : Localization.Away (tY K) := ↑(g1Unit K)
  let V : Localization.Away (tY K) := ↑((g1Unit K)⁻¹)
  let A : Localization.Away (tY K) := algebraMap (E37ChartYRing K) (Localization.Away (tY K)) (sY K)
  let B : Localization.Away (tY K) := algebraMap (E37ChartYRing K) (Localization.Away (tY K)) (tY K)
  have hWV : W * V = 1 := Units.mul_inv (g1Unit K)
  have hA : g1Poly K (MvPolynomial.X 0) = A * V := by simp [g1Poly, g1Vals, A, V]
  have hB : g1Poly K (MvPolynomial.X 1) = -1 - V := by simp [g1Poly, g1Vals, V]
  have hC0 : g1Poly K (MvPolynomial.C 0) = 0 := by simp [g1Poly]
  have hC1 : g1Poly K (MvPolynomial.C 1) = 1 := by simp [g1Poly]
  have hrep : g1Poly K (S2801E37Polynomial K) =
      (-1 - V)^2 + (-1 - V) - (A*V)^3 + A*V := by
    simp only [S2801E37Polynomial, S2801E37Curve,
      LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial,
      map_add, map_mul, map_pow, map_sub, hA, hB, hC0, hC1,
      MvPolynomial.eval₂Hom_C, map_one, map_zero, map_neg]
    ring
  have hpow : W = B := by
    change (↑(g1Unit K) : Localization.Away (tY K)) = B
    rw [show (↑(g1Unit K) : Localization.Away (tY K)) =
      algebraMap (E37ChartYRing K) (Localization.Away (tY K)) (tY K) from
      IsUnit.unit_spec _]
  calc
    W^3 * g1Poly K (S2801E37Polynomial K)
        = W^3 * ((-1 - V)^2 + (-1 - V) - (A*V)^3 + A*V) := by rw [hrep]
    _ = W^2 + W - A^3 + A*W^2 := by
      have h1 : W^3 * V = W^2 := by
        calc W^3 * V = W^2 * (W*V) := by ring
          _ = W^2 := by rw [hWV]; ring
      have h2 : W^3 * V^2 = W := by
        calc W^3 * V^2 = W * (W*V)^2 := by ring
          _ = W := by rw [hWV]; ring
      have h3 : W^3 * V^3 = 1 := by
        calc W^3 * V^3 = (W*V)^3 := by ring
          _ = 1 := by rw [hWV]; norm_num
      rw [show (-1 - V)^2 + (-1 - V) - (A*V)^3 + A*V = V + V^2 - A^3*V^3 + A*V by ring]
      calc
        W^3 * (V + V^2 - A^3*V^3 + A*V)
            = W^3*V + W^3*V^2 - A^3*(W^3*V^3) + A*(W^3*V) := by ring
        _ = W^2 + W - A^3 + A*W^2 := by rw [h1,h2,h3]; ring
    _ = -A^3 + A*B^2 + B + B^2 := by
      rw [hpow]; ring
    _ = -algebraMap (E37ChartYRing K) (Localization.Away (tY K))
        ((sY K)^3 - sY K*(tY K)^2 - tY K - (tY K)^2) := by
      rw [show algebraMap (E37ChartYRing K) (Localization.Away (tY K))
          ((sY K)^3 - sY K*(tY K)^2 - tY K - (tY K)^2)
        = A^3 - A*B^2 - B - B^2 by simp [A, B, map_sub, map_mul, map_pow]]
      ring

theorem g1Poly_relation :
    g1Poly K (S2801E37Polynomial K) = 0 := by
  have hscale := g1Poly_scale (K := K)
  have hu : IsUnit (↑(g1Unit K) : Localization.Away (tY K)) :=
    ⟨g1Unit K, rfl⟩
  have hzero : (↑(g1Unit K) : Localization.Away (tY K))^3 *
      g1Poly K (S2801E37Polynomial K) = 0 := by
    rw [hscale, g1_hrel]
    simp
  exact (IsUnit.mul_right_inj (hu.pow 3)).mp (by simpa using hzero)


noncomputable def g0Ring :
    E37ChartYRing K →+* S2853ChartYNegRing K :=
  Ideal.Quotient.lift (E37ChartYIdeal K) (g0Poly K) (by
    have hle : E37ChartYIdeal K ≤ RingHom.ker (g0Poly K) := by
      intro b hb
      rw [E37ChartYIdeal, Ideal.mem_span_singleton] at hb
      rcases hb with ⟨c, rfl⟩
      rw [RingHom.mem_ker, map_mul, g0Poly_relation K, zero_mul]
    intro a ha
    exact RingHom.mem_ker.mp (hle ha))

noncomputable def g0Scheme :
    V0 K ⟶ S2820E37ProjectiveScheme K :=
  Spec.map (CommRingCat.ofHom (g0Ring K)) ≫ S2820E37ChartYMap K

noncomputable def g1Ring :
    S2801E37CoordinateRing K →+* Localization.Away (tY K) :=
  Ideal.Quotient.lift (S2801E37Ideal K) (g1Poly K) (by
    have hle : S2801E37Ideal K ≤ RingHom.ker (g1Poly K) := by
      intro b hb
      rw [S2801E37Ideal, Ideal.mem_span_singleton] at hb
      rcases hb with ⟨c, rfl⟩
      rw [RingHom.mem_ker, map_mul, g1Poly_relation K, zero_mul]
    intro a ha
    exact RingHom.mem_ker.mp (hle ha))

noncomputable def g1Scheme :
    V1 K ⟶ S2820E37ProjectiveScheme K :=
  Spec.map (CommRingCat.ofHom (g1Ring K)) ≫ S2820E37ChartZMap K


noncomputable abbrev f0 : V0 K ⟶ E37ChartYScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)))

noncomputable abbrev f1 : V1 K ⟶ E37ChartYScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (E37ChartYRing K) (Localization.Away (tY K))))

noncomputable abbrev coverObj : Bool → Scheme
  | false => V0 K
  | true => V1 K

noncomputable abbrev coverMap : (b : Bool) → coverObj K b ⟶ E37ChartYScheme K
  | false => f0 K
  | true => f1 K

theorem chartYCover_covers :
    ∀ x : E37ChartYScheme K, ∃ b y, coverMap K b y = x := by
  intro x
  by_cases ht : tY K ∈ x.asIdeal
  · have h1t : 1 + tY K ∉ x.asIdeal := by
      intro h
      have h1 : (1 : E37ChartYRing K) ∈ x.asIdeal := by
        have hsub := x.asIdeal.sub_mem h ht
        simpa using hsub
      exact x.isPrime.ne_top ((Ideal.eq_top_iff_one x.asIdeal).mpr h1)
    have hmem : x ∈ (↑(PrimeSpectrum.basicOpen (1 + tY K)) :
        Set (PrimeSpectrum (E37ChartYRing K))) :=
      (PrimeSpectrum.mem_basicOpen _ _).mpr h1t
    rw [← PrimeSpectrum.localization_away_comap_range
      (S2853ChartYNegRing K) (1 + tY K)] at hmem
    obtain ⟨y, hy⟩ := hmem
    refine ⟨false, y, ?_⟩
    change (Spec.map (CommRingCat.ofHom (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K))) y) = x
    exact hy
  · have hmem : x ∈ (↑(PrimeSpectrum.basicOpen (tY K)) :
        Set (PrimeSpectrum (E37ChartYRing K))) :=
      (PrimeSpectrum.mem_basicOpen _ _).mpr ht
    rw [← PrimeSpectrum.localization_away_comap_range
      (Localization.Away (tY K)) (tY K)] at hmem
    obtain ⟨y, hy⟩ := hmem
    refine ⟨true, y, ?_⟩
    change (Spec.map (CommRingCat.ofHom (algebraMap (E37ChartYRing K) (Localization.Away (tY K)))) y) = x
    exact hy

noncomputable def chartYCover : (E37ChartYScheme K).OpenCover :=
  Scheme.Cover.mkOfCovers (P := IsOpenImmersion) Bool (coverObj K) (coverMap K)
    (chartYCover_covers K)
    (by
      intro b
      cases b
      · exact AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway
          (R := CommRingCat.of (E37ChartYRing K)) (1 + tY K)
      · exact AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway
          (R := CommRingCat.of (E37ChartYRing K)) (tY K))

noncomputable def chartYNegGMap (b : Bool) :
    (chartYCover K).X b ⟶ S2820E37ProjectiveScheme K :=
  match b with
  | false => g0Scheme K
  | true => g1Scheme K


/-- The chart-Y negation morphism to the glued projective scheme, conditional
on compatibility on the two-chart overlap. -/
noncomputable def chartYNegGluedHom
    (hf : ∀ x y,
      pullback.fst ((chartYCover K).f x) ((chartYCover K).f y) ≫
          chartYNegGMap K x =
        pullback.snd ((chartYCover K).f x) ((chartYCover K).f y) ≫
          chartYNegGMap K y) :
    E37ChartYScheme K ⟶ S2820E37ProjectiveScheme K :=
  (chartYCover K).glueMorphisms (chartYNegGMap K) hf

end LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
end
