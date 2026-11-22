/-
Copyright (c) 2026 The LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Legendre even-sextic map on the projective line

This file constructs, independently of any other file, the projective-point map attached to the
classical Legendre pair of binary sextics

* `LegendreF K v = 256 * (v 0 ^ 2 - v 0 * v 1 + v 1 ^ 2) ^ 3`
* `LegendreG K v = v 0 ^ 2 * v 1 ^ 2 * (v 0 - v 1) ^ 2`,

namely the map `[X : Y] ↦ [F(X,Y) : G(X,Y)]` on `ℙ K (Fin 2 → K)`.  This is the projective
shadow of the Legendre parameter-to-`j` correspondence used in the elliptic/moduli reduction
step of IUT IV: the `λ`-line is covered six-to-one by the `j`-line, and the pair above exhibits
over any field of characteristic zero the essential feature that the two sextics have no common
projective zero while sharing the six preimages of a general point.  The Legendre-map statements
below are therefore made over characteristic-zero fields (in characteristic two the numeral
`256` vanishes and the pair degenerates); the general even-sextic-map machinery is stated
without characteristic hypotheses.

The construction uses Mathlib's actual projectivization quotient `Projectivization K (Fin 2 → K)`
and its quotient/lifting API (`Projectivization.mk`, `Projectivization.lift`,
`Projectivization.mk_eq_mk_iff`, `Projectivization.map`); no custom pair-set model of `P¹` is
introduced.

## Main results

* `LegendreF`, `LegendreG` : the two binary sextics as functions on `Fin 2 → K`.
* `LegendreSextics_smul_six` : both are homogeneous of degree six.
* `LegendreSextics_apply_eq_zero` : over a characteristic-zero field, their only common zero is
  the origin.
* `LegendreSextics_apply_ne_zero` : over a characteristic-zero field, on a nonzero vector at
  least one of the two sextics does not vanish.
* `EvenSexticMap` : the general projective point map attached to a pair of sextics which is
  proportional on expanded pairs and has no common zero.  Its quotient descent is
  `EvenSexticMap.toFun`.
* `EvenSexticMap.lift_mk` : the computation rule of that projective map on a representative.
* `LegendreProjectiveMap` : the concrete map `[X : Y] ↦ [F(X,Y) : G(X,Y)]`.
* `LegendreProjectiveMap_coords` : its value on the class of `(X, Y)`.
* `legSameRatios_iff_eq` and `legSameRatios_map_legendreMap` : explicit well-definedness of the
  Legendre map with respect to proportional representatives.
* `LegendreF_affine`, `LegendreG_affine`, `LegendreProjectiveMap_affineChart` : on the affine
  chart `[λ : 1]` the map is `λ ↦ [256 * (λ^2 - λ + 1)^3 / (λ^2 * (1 - λ)^2) : 1]`, stated
  without division as a ratio relation between the two coordinate vectors.
* `LegendreProjectiveMap_boundary_zero`, `..._boundary_one`, `..._boundary_infty`,
  `LegendreProjectiveMap_boundary_points` : the three boundary points `0`, `1`, `∞` all have
  image the same point `∞ = [1 : 0]`.
* `legCoordsMap`, `legCoordsMap_projective`, `legCoordsMap_projective_formula`,
  `legCoordsMap_projective_coords`, `legCoordsMap_naturality_legendre`, `LegendreBaseChange`,
  `LegendreBaseChange_pushforward_commutes` : base change of the projective point map along a
  field homomorphism, as compatibility of the map with the semilinear pushforward on projective
  points for equal diagonal scaling.

## Scope

The results here concern projective *points* only.  Nothing below claims that
`LegendreProjectiveMap` is a scheme morphism, nor that the six-to-one behaviour is a
scheme-theoretic degree statement: the algebraic content established here is that both forms are
homogeneous of degree six, that they have no common projective zero, and that the induced map on
projective points is well defined and compatible with base change of the coordinate line.

## References

* The Legendre family `y^2 = x(x-1)(x-λ)` and its classical `j`-invariant; see e.g. Silverman,
  *The Arithmetic of Elliptic Curves*, III.1.
-/

module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Projectivization.Constructions

@[expose] public section

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace LeanFormal.IUT

/-! ### The two sextics -/

section Sextics

variable {K : Type*} [Field K]

/-- The binary sextic `F(X,Y) = 256 * (X^2 - X*Y + Y^2)^3` attached to the Legendre family,
as a function on the coordinate space `Fin 2 → K`. -/
def LegendreF (K : Type*) [Field K] : (Fin 2 → K) → K :=
  fun v => 256 * (v 0 ^ 2 - v 0 * v 1 + v 1 ^ 2) ^ 3

/-- The binary sextic `G(X,Y) = X^2 * Y^2 * (X - Y)^2` attached to the Legendre family,
as a function on the coordinate space `Fin 2 → K`. -/
def LegendreG (K : Type*) [Field K] : (Fin 2 → K) → K :=
  fun v => v 0 ^ 2 * v 1 ^ 2 * (v 0 - v 1) ^ 2

@[simp]
theorem LegendreF_apply (v : Fin 2 → K) :
    LegendreF K v = 256 * (v 0 ^ 2 - v 0 * v 1 + v 1 ^ 2) ^ 3 := rfl

@[simp]
theorem LegendreG_apply (v : Fin 2 → K) :
    LegendreG K v = v 0 ^ 2 * v 1 ^ 2 * (v 0 - v 1) ^ 2 := rfl

theorem legendre_numeral_two_ne_zero : (2 : ℕ) ≠ 0 := by norm_num

theorem legendre_numeral_three_ne_zero : (3 : ℕ) ≠ 0 := by norm_num

/-- The numeral `256` is nonzero in any field of characteristic zero. -/
theorem legendre_numeral_256_ne_zero (K : Type*) [Field K] [CharZero K] : (256 : K) ≠ 0 := by
  norm_num

theorem legendre_numeral_256_ne_zero' [CharZero K] : (256 : K) ≠ 0 :=
  legendre_numeral_256_ne_zero K

/-- Both sextics are homogeneous of degree six: scaling the coordinate vector by `t` multiplies
each of them by `t ^ 6`. -/
theorem LegendreSextics_smul_six (t : K) (v : Fin 2 → K) :
    LegendreF K (t • v) = t ^ 6 * LegendreF K v ∧
      LegendreG K (t • v) = t ^ 6 * LegendreG K v := by
  have h0 : (t • v) 0 = t * (v 0) := by simp
  have h1 : (t • v) 1 = t * (v 1) := by simp
  simp only [LegendreF_apply, LegendreG_apply, h0, h1]
  constructor <;> ring

/-- Over a characteristic-zero field the two Legendre sextics have exactly one common zero, the
origin. -/
theorem LegendreSextics_apply_eq_zero [CharZero K] (v : Fin 2 → K)
    (hF : LegendreF K v = 0) (hG : LegendreG K v = 0) : v = 0 := by
  have h2 : (2 : ℕ) ≠ 0 := legendre_numeral_two_ne_zero
  have hF' : 256 * (v 0 ^ 2 - v 0 * v 1 + v 1 ^ 2) ^ 3 = 0 := by simpa using hF
  have hG' : v 0 ^ 2 * v 1 ^ 2 * (v 0 - v 1) ^ 2 = 0 := by simpa using hG
  have hquad : v 0 ^ 2 - v 0 * v 1 + v 1 ^ 2 = 0 := by
    rcases mul_eq_zero.mp hF' with h | h
    · exact absurd h (legendre_numeral_256_ne_zero K)
    · exact (pow_eq_zero_iff (legendre_numeral_three_ne_zero)).mp h
  have hprod : v 0 = 0 ∨ v 1 = 0 ∨ v 0 = v 1 := by
    rcases mul_eq_zero.mp hG' with h | h
    · rcases mul_eq_zero.mp h with h0 | h1
      · exact Or.inl ((pow_eq_zero_iff h2).mp h0)
      · exact Or.inr (Or.inl ((pow_eq_zero_iff h2).mp h1))
    · exact Or.inr (Or.inr (sub_eq_zero.mp ((pow_eq_zero_iff h2).mp h)))
  rcases hprod with h0 | h1 | hsub
  · have hv1 : v 1 = 0 := by
      have hsq : v 1 ^ 2 = 0 := by
        have h := hquad
        rw [h0] at h
        ring_nf at h
        exact h
      exact (pow_eq_zero_iff h2).mp hsq
    funext i
    fin_cases i <;> simp [h0, hv1]
  · have hv0 : v 0 = 0 := by
      have hsq : v 0 ^ 2 = 0 := by
        have h := hquad
        rw [h1] at h
        ring_nf at h
        exact h
      exact (pow_eq_zero_iff h2).mp hsq
    funext i
    fin_cases i <;> simp [h1, hv0]
  · have hsq : v 0 ^ 2 = 0 := by
      have h := hquad
      rw [← hsub] at h
      ring_nf at h
      exact h
    have hv0 : v 0 = 0 := (pow_eq_zero_iff h2).mp hsq
    funext i
    have hv1 : v 1 = 0 := by rw [← hsub, hv0]
    fin_cases i <;> simp [hv0, hv1]

/-- Over a characteristic-zero field, on a nonzero coordinate vector at least one of the two
Legendre sextics does not vanish. -/
theorem LegendreSextics_apply_ne_zero [CharZero K] (v : Fin 2 → K) (hv : v ≠ 0) :
    LegendreF K v ≠ 0 ∨ LegendreG K v ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (LegendreSextics_apply_eq_zero v h.1 h.2)

/-- The sextic pair takes the origin to the origin. -/
theorem LegendreSextics_apply_zero : LegendreF K 0 = 0 ∧ LegendreG K 0 = 0 := by
  constructor <;> simp only [LegendreF, LegendreG] <;> norm_num

end Sextics

/-! ### Proportional pairs of coordinate vectors -/

section Ratios

variable {K : Type*} [Field K]

/-- Two coordinate vectors on `K²` determine the same point of the projective line exactly when
each is a nonzero scalar multiple of the other.  This is stated directly on the coordinate vectors
used by the sextic pair. -/
def legSameRatios (v w : Fin 2 → K) : Prop :=
  ∃ u : Kˣ, u • w = v

/-- `legSameRatios` is exactly equality of the corresponding projective points. -/
theorem legSameRatios_iff_eq {v w : Fin 2 → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    legSameRatios v w ↔ Projectivization.mk K v hv = Projectivization.mk K w hw :=
  (Projectivization.mk_eq_mk_iff K v w hv hw).symm

end Ratios

/-! ### The general even-sextic projective map -/

section EvenSextic

/-- Proportionality of a coordinate formula under expansion of the representative: the sixth
power of the expansion factor acts as a scalar.  This is the hypothesis which makes the pair of
binary sextics descend to the projectivization. -/
def ProportionalOnExpansion {K : Type*} [Field K]
    (halfMap : {v : Fin 2 → K // v ≠ 0} → ℙ K (Fin 2 → K)) : Prop :=
  ∀ (a b : {v : Fin 2 → K // v ≠ 0}) (t : K), a = t • (b : Fin 2 → K) → halfMap a = halfMap b

/-- A pair of binary sextics on `K²` which is proportional on expanded pairs (with the sixth
power of the expansion factor) and has no common zero.  Such a pair defines a map on
`ℙ K (Fin 2 → K)` by `[X : Y] ↦ [F(X,Y) : G(X,Y)]`; the well-definedness of that map on
projective points is the content of `EvenSexticMap.toFun`. -/
structure EvenSexticMap (K : Type*) [Field K] where
  /-- The first binary sextic of the pair. -/
  first : (Fin 2 → K) → K
  /-- The second binary sextic of the pair. -/
  second : (Fin 2 → K) → K
  /-- The pair, read as a map from nonzero coordinate vectors into the projective line. -/
  halfMap : {v : Fin 2 → K // v ≠ 0} → ℙ K (Fin 2 → K)
  /-- The pair has no common zero. -/
  no_common_zero : ∀ v : Fin 2 → K, first v = 0 → second v = 0 → v = 0
  /-- Proportionality of the pair under expansion: this is the hypothesis that makes the
  coordinate formula descend to the quotient. -/
  proportional_on_products : ProportionalOnExpansion halfMap

namespace EvenSexticMap

/-- The projective-point map attached to an even sextic pair.  It is defined by descending the
coordinate formula along the projectivization quotient. -/
def toFun {K : Type*} [Field K] (P : EvenSexticMap K) : ℙ K (Fin 2 → K) → ℙ K (Fin 2 → K) :=
  Projectivization.lift P.halfMap P.proportional_on_products

/-- Computation rule for the descended map on a representative. -/
@[simp]
theorem lift_mk {K : Type*} [Field K] (P : EvenSexticMap K)
    (v : Fin 2 → K) (hv : v ≠ 0) :
    P.toFun (Projectivization.mk K v hv) = P.halfMap (Subtype.mk v hv) := by
  rw [toFun, Projectivization.lift_mk]

/-- An even sextic map induces a function on the projective line. -/
def projectiveMap {K : Type*} [Field K] (P : EvenSexticMap K) :
    ℙ K (Fin 2 → K) → ℙ K (Fin 2 → K) :=
  P.toFun

@[simp]
theorem projectiveMap_apply {K : Type*} [Field K] (P : EvenSexticMap K)
    (x : ℙ K (Fin 2 → K)) :
    P.projectiveMap x = P.toFun x := rfl

end EvenSexticMap

end EvenSextic

/-! ### The Legendre even-sextic map -/

section Legendre

variable {K : Type*} [Field K]

/-- The coordinate pair `[F v : G v]` is nonzero whenever `v` is (characteristic zero). -/
theorem legPair_nonzero [CharZero K] (v : Fin 2 → K) (hv : v ≠ 0) :
    ![LegendreF K v, LegendreG K v] ≠ 0 := by
  intro h
  have h0 : LegendreF K v = 0 := by
    have := congrFun h 0
    simpa using this
  have h1 : LegendreG K v = 0 := by
    have := congrFun h 1
    simpa using this
  exact hv (LegendreSextics_apply_eq_zero v h0 h1)

/-- The coordinate formula `[X : Y] ↦ [F(X,Y) : G(X,Y)]` for the Legendre sextic pair, as a map
on nonzero coordinate vectors into the projective line.  Since `F` and `G` have no common zero
(characteristic zero), the target vector is nonzero. -/
def legImg [CharZero K] (v : {v : Fin 2 → K // v ≠ 0}) : ℙ K (Fin 2 → K) :=
  Projectivization.mk K ![LegendreF K (v : Fin 2 → K), LegendreG K (v : Fin 2 → K)]
    (legPair_nonzero (v : Fin 2 → K) v.2)

/-- `legImg ⟨v, hv⟩` is the projective point `[F v : G v]`, with the nonzero proof from
`legPair_nonzero`. -/
theorem legImg_apply [CharZero K] (v : Fin 2 → K) (hv : v ≠ 0) :
    legImg ⟨v, hv⟩ =
      Projectivization.mk K ![LegendreF K v, LegendreG K v] (legPair_nonzero v hv) :=
  rfl

/-- The coordinate pair `[F v : G v]` is nonzero when at least one of the two sextics does not
vanish. -/
theorem legPair_nonzero_of_ne_zero (v : Fin 2 → K)
    (h : LegendreF K v ≠ 0 ∨ LegendreG K v ≠ 0) :
    ![LegendreF K v, LegendreG K v] ≠ 0 := by
  intro hzero
  have h0 : LegendreF K v = 0 := by
    have := congrFun hzero 0
    simpa using this
  have h1 : LegendreG K v = 0 := by
    have := congrFun hzero 1
    simpa using this
  rcases h with h | h
  · exact h h0
  · exact h h1

/-- Scalar multiples of a nonzero representative have the same image under the sextic formula:
this is the well-definedness of `legImg` on the projective line, and the reason it descends to a
map of projective points. -/
theorem legImg_smul [CharZero K] (t : K) (v : Fin 2 → K) (hv : v ≠ 0) (ht : t ≠ 0) :
    legImg ⟨t • v, smul_ne_zero ht hv⟩ = legImg ⟨v, hv⟩ := by
  have h := LegendreSextics_smul_six (K := K) t v
  rw [legImg_apply (t • v) (smul_ne_zero ht hv), legImg_apply v hv]
  exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr (by
    refine ⟨Units.mk0 (t ^ 6) (pow_ne_zero 6 ht), ?_⟩
    change (t ^ 6 : K) • ![LegendreF K v, LegendreG K v] =
      ![LegendreF K (t • v), LegendreG K (t • v)]
    rw [h.1, h.2]
    ext i
    fin_cases i <;> simp)

/-- The Legendre pair, packaged as an even sextic map. -/
def legendreEvenSexticMap [CharZero K] : EvenSexticMap K where
  first := LegendreF K
  second := LegendreG K
  halfMap := legImg
  no_common_zero := fun v hF hG => LegendreSextics_apply_eq_zero v hF hG
  proportional_on_products := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ t rfl
    exact legImg_smul t w hw (by
      rintro rfl
      exact hv (by simp))

/-- The Legendre projective point map `[X : Y] ↦ [F(X,Y) : G(X,Y)]` on `ℙ K (Fin 2 → K)`. -/
def LegendreProjectiveMap [CharZero K] : ℙ K (Fin 2 → K) → ℙ K (Fin 2 → K) :=
  legendreEvenSexticMap.toFun

/-- The Legendre map is the function underlying the Legendre even sextic map. -/
theorem LegendreProjectiveMap_eq_coe [CharZero K] :
    (LegendreProjectiveMap (K := K)) = (legendreEvenSexticMap (K := K)).projectiveMap := rfl

/-- The computation rule for the Legendre map on the class of a nonzero coordinate vector. -/
@[simp]
theorem LegendreProjectiveMap_coords [CharZero K] (v : Fin 2 → K) (hv : v ≠ 0) :
    LegendreProjectiveMap (Projectivization.mk K v hv) = legImg ⟨v, hv⟩ :=
  EvenSexticMap.lift_mk legendreEvenSexticMap v hv

/-- Proportional representatives have the same image: the well-definedness statement for the
Legendre map at the level of coordinate vectors. -/
theorem legSameRatios_map_legendreMap [CharZero K] {v w : Fin 2 → K} (hv : v ≠ 0)
    (hw : w ≠ 0) (ht : legSameRatios v w) :
    legImg ⟨v, hv⟩ = legImg ⟨w, hw⟩ := by
  obtain ⟨u, hu⟩ := ht
  have hEq : (⟨v, hv⟩ : {x : Fin 2 → K // x ≠ 0}) =
      ⟨(u : K) • w, smul_ne_zero (Units.ne_zero u) hw⟩ :=
    Subtype.ext hu.symm
  rw [hEq]
  exact legImg_smul (u : K) w hw (Units.ne_zero u)

end Legendre

/-! ### The affine chart and the three boundary points -/

section AffineChart

variable {K : Type*} [Field K]

/-- The point `[t : 1]` of the projective line, as a coordinate vector. -/
def affineVec (K : Type*) [Field K] : K → (Fin 2 → K) := fun t => ![t, 1]

@[simp]
theorem affineVec_zero (t : K) : affineVec K t 0 = t := rfl

@[simp]
theorem affineVec_one (t : K) : affineVec K t 1 = 1 := rfl

/-- The value of the first sextic on the affine chart `[t : 1]`. -/
theorem LegendreF_affine (t : K) :
    LegendreF K (affineVec K t) = 256 * (t ^ 2 - t + 1) ^ 3 := by
  have h0 : (affineVec K t) 0 = t := rfl
  have h1 : (affineVec K t) 1 = 1 := rfl
  rw [LegendreF_apply, h0, h1]
  ring

/-- The value of the second sextic on the affine chart `[t : 1]`. -/
theorem LegendreG_affine (t : K) :
    LegendreG K (affineVec K t) = t ^ 2 * (1 - t) ^ 2 := by
  have h0 : (affineVec K t) 0 = t := rfl
  have h1 : (affineVec K t) 1 = 1 := rfl
  rw [LegendreG_apply, h0, h1]
  ring

/-- The image of the affine chart point `[λ : 1]` (for `λ ≠ 0, 1`) is the projective point with
coordinate vector `[256 * (λ^2 - λ + 1)^3 : λ^2 * (1 - λ)^2]`.  Since `λ * (1 - λ) ≠ 0`, this is
the usual `[256 * (λ^2 - λ + 1)^3 / (λ^2 * (1 - λ)^2) : 1]`; the statement is kept division-free
in the form of a ratio relation between the two coordinate vectors. -/
theorem LegendreProjectiveMap_affineChart [CharZero K] (lam : K) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    LegendreProjectiveMap (Projectivization.mk K (affineVec K lam) (by
        intro hv
        have := congrFun hv 1
        simp [affineVec] at this)) =
      Projectivization.mk K
        ![256 * (lam ^ 2 - lam + 1) ^ 3, lam ^ 2 * (1 - lam) ^ 2]
        (by
          intro h
          have h2 : lam ^ 2 * (1 - lam) ^ 2 = 0 := by
            have := congrFun h 1
            simpa using this
          exact (mul_ne_zero (pow_ne_zero 2 h0) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h1))))
            h2) := by
  have hne : affineVec K lam ≠ 0 := by
    intro hv
    have := congrFun hv 1
    simp [affineVec] at this
  rw [LegendreProjectiveMap_coords (affineVec K lam) hne, legImg_apply (affineVec K lam) hne]
  refine (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨1, ?_⟩
  show (1 : K) • ![256 * (lam ^ 2 - lam + 1) ^ 3, lam ^ 2 * (1 - lam) ^ 2] =
    ![LegendreF K (affineVec K lam), LegendreG K (affineVec K lam)]
  rw [one_smul]
  ext i
  fin_cases i
  · exact (LegendreF_affine lam).symm
  · exact (LegendreG_affine lam).symm

/-- The point at infinity `[1 : 0]` of the projective line. -/
def projectivePointAtInfinity (K : Type*) [Field K] : ℙ K (Fin 2 → K) :=
  Projectivization.mk K ![1, 0] (by
    intro h
    have := congrFun h 0
    simp at this)

/-- Every point of the boundary `G = 0` has image the point at infinity `[1 : 0]`. -/
theorem LegendreProjectiveMap_eq_infinity_of_G_eq_zero [CharZero K] (v : Fin 2 → K) (hv : v ≠ 0)
    (hG : LegendreG K v = 0) :
    LegendreProjectiveMap (Projectivization.mk K v hv) = projectivePointAtInfinity K := by
  rw [LegendreProjectiveMap_coords v hv, legImg_apply v hv]
  exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr (by
    refine ⟨Units.mk0 (LegendreF K v) (by
      intro hF
      exact hv (LegendreSextics_apply_eq_zero v hF hG)), ?_⟩
    change (LegendreF K v : K) • ![1, 0] = ![LegendreF K v, LegendreG K v]
    rw [hG]
    ext i
    fin_cases i <;> simp)

/-- The boundary point `0 = [0 : 1]` maps to infinity. -/
theorem LegendreProjectiveMap_boundary_zero [CharZero K] :
    LegendreProjectiveMap (Projectivization.mk K (affineVec K 0) (by
        intro hv
        have := congrFun hv 1
        simp [affineVec] at this)) = projectivePointAtInfinity K := by
  apply LegendreProjectiveMap_eq_infinity_of_G_eq_zero
  rw [LegendreG_affine]
  ring

/-- The boundary point `1 = [1 : 1]` maps to infinity. -/
theorem LegendreProjectiveMap_boundary_one [CharZero K] :
    LegendreProjectiveMap (Projectivization.mk K (affineVec K 1) (by
        intro hv
        have := congrFun hv 1
        simp [affineVec] at this)) = projectivePointAtInfinity K := by
  apply LegendreProjectiveMap_eq_infinity_of_G_eq_zero
  rw [LegendreG_affine]
  ring

/-- The point at infinity `[1 : 0]` maps to itself. -/
theorem LegendreProjectiveMap_boundary_infty [CharZero K] :
    LegendreProjectiveMap (projectivePointAtInfinity K) = projectivePointAtInfinity K := by
  unfold projectivePointAtInfinity
  apply LegendreProjectiveMap_eq_infinity_of_G_eq_zero
  simp [LegendreG]

/-- All three boundary points `0`, `1`, `∞` of the Legendre parameter line have image the same
point, namely `∞ = [1 : 0]`. -/
theorem LegendreProjectiveMap_boundary_points [CharZero K] :
    LegendreProjectiveMap (Projectivization.mk K (affineVec K 0) (by
        intro hv
        have := congrFun hv 1
        simp [affineVec] at this)) = projectivePointAtInfinity K ∧
      LegendreProjectiveMap (Projectivization.mk K (affineVec K 1) (by
        intro hv
        have := congrFun hv 1
        simp [affineVec] at this)) = projectivePointAtInfinity K ∧
      LegendreProjectiveMap (projectivePointAtInfinity K) = projectivePointAtInfinity K :=
  ⟨LegendreProjectiveMap_boundary_zero, LegendreProjectiveMap_boundary_one,
    LegendreProjectiveMap_boundary_infty⟩

end AffineChart

/-! ### Base change along a field homomorphism -/

section BaseChange

variable {K L : Type*} [Field K] [Field L] {σ : K →+* L}

/-- The diagonal semilinear map `(x, y) ↦ (a * σ x, b * σ y)` on coordinate vectors; this is the
concrete form of the base change of the coordinate line used by the Legendre map. -/
def legCoordsMap (a b : L) : (Fin 2 → K) →ₛₗ[σ] (Fin 2 → L) where
  toFun := fun v => ![a * σ (v 0), b * σ (v 1)]
  map_add' := by
    intro v w
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' := by
    intro c v
    ext i
    fin_cases i <;> simp [mul_left_comm]

@[simp]
theorem legCoordsMap_apply_zero (a b : L) (v : Fin 2 → K) :
    legCoordsMap (σ := σ) a b v 0 = a * σ (v 0) := rfl

@[simp]
theorem legCoordsMap_apply_one (a b : L) (v : Fin 2 → K) :
    legCoordsMap (σ := σ) a b v 1 = b * σ (v 1) := rfl

/-- For equal diagonal entries the semilinear coordinate map is scalar multiplication of the
coefficient pushforward `v ↦ σ ∘ v`. -/
theorem legCoordsMap_self (a : L) (v : Fin 2 → K) :
    legCoordsMap (σ := σ) a a v = a • (fun i => σ (v i)) := by
  ext i
  fin_cases i <;> rfl

/-- The first sextic commutes with coefficient change: `F` is defined over `ℤ`. -/
theorem LegendreF_map (σ : K →+* L) (v : Fin 2 → K) :
    LegendreF L (fun i => σ (v i)) = σ (LegendreF K v) := by
  simp only [LegendreF_apply, map_mul, map_pow, map_sub, map_add, map_ofNat]

/-- The second sextic commutes with coefficient change: `G` is defined over `ℤ`. -/
theorem LegendreG_map (σ : K →+* L) (v : Fin 2 → K) :
    LegendreG L (fun i => σ (v i)) = σ (LegendreG K v) := by
  simp only [LegendreG_apply, map_mul, map_pow, map_sub]

/-- Base change of the first sextic under equal dilation:
`F (a • (σ ∘ v)) = a ^ 6 * σ (F v)`. -/
theorem LegendreF_map_smul (a : L) (v : Fin 2 → K) :
    LegendreF L ((legCoordsMap (σ := σ) a a) v) = a ^ 6 * σ (LegendreF K v) := by
  rw [legCoordsMap_self (σ := σ) a,
    (LegendreSextics_smul_six (K := L) a (fun i => σ (v i))).1, LegendreF_map]

/-- Base change of the second sextic under equal dilation:
`G (a • (σ ∘ v)) = a ^ 6 * σ (G v)`. -/
theorem LegendreG_map_smul (a : L) (v : Fin 2 → K) :
    LegendreG L ((legCoordsMap (σ := σ) a a) v) = a ^ 6 * σ (LegendreG K v) := by
  rw [legCoordsMap_self (σ := σ) a,
    (LegendreSextics_smul_six (K := L) a (fun i => σ (v i))).2, LegendreG_map]

/-- The diagonal semilinear map is injective when the diagonal entries are nonzero. -/
theorem legCoordsMap_injective (a b : L) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (legCoordsMap (σ := σ) a b) := by
  intro v w hv
  have h0 : (legCoordsMap (σ := σ) a b) v 0 = (legCoordsMap (σ := σ) a b) w 0 := congrFun hv 0
  have h1 : (legCoordsMap (σ := σ) a b) v 1 = (legCoordsMap (σ := σ) a b) w 1 := congrFun hv 1
  rw [legCoordsMap_apply_zero, legCoordsMap_apply_zero] at h0
  rw [legCoordsMap_apply_one, legCoordsMap_apply_one] at h1
  have hv0 : v 0 = w 0 := σ.injective (mul_left_cancel₀ ha h0)
  have hv1 : v 1 = w 1 := σ.injective (mul_left_cancel₀ hb h1)
  funext i
  fin_cases i
  · simpa using hv0
  · simpa using hv1

/-- The projective map induced by the diagonal semilinear map. -/
def legCoordsMap_projective (a b : L) (ha : a ≠ 0) (hb : b ≠ 0) :
    ℙ K (Fin 2 → K) → ℙ L (Fin 2 → L) :=
  Projectivization.map (legCoordsMap (σ := σ) a b) (legCoordsMap_injective a b ha hb)

/-- The sextic pair evaluated on the base-changed coordinate vector is proportional to the
base-changed sextic values, for equal diagonal scaling.  The unit ratio is `a ^ 6`. -/
theorem legCoordsMap_projective_formula (a : L) (ha : a ≠ 0) (v : Fin 2 → K) :
    legSameRatios
      ![LegendreF L ((legCoordsMap (σ := σ) a a) v),
        LegendreG L ((legCoordsMap (σ := σ) a a) v)]
      ![σ (LegendreF K v), σ (LegendreG K v)] := by
  refine ⟨Units.mk0 (a ^ 6) (pow_ne_zero 6 ha), ?_⟩
  rw [LegendreF_map_smul (σ := σ) a, LegendreG_map_smul (σ := σ) a]
  ext i
  fin_cases i <;> simp

/-- The diagonal semilinear map sends a coordinate vector to zero only if the vector itself is
zero (for nonzero diagonal entries). -/
theorem legCoordsMap_eq_zero_iff (a b : L) (ha : a ≠ 0) (hb : b ≠ 0) (v : Fin 2 → K) :
    (legCoordsMap (σ := σ) a b) v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have h0 : (legCoordsMap (σ := σ) a b) v 0 = 0 := congrFun hv 0
    have h1 : (legCoordsMap (σ := σ) a b) v 1 = 0 := congrFun hv 1
    rw [legCoordsMap_apply_zero] at h0
    rw [legCoordsMap_apply_one] at h1
    have hσ0 : σ (v 0) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h ha
      · exact h
    have hσ1 : σ (v 1) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hb
      · exact h
    have hv0 : v 0 = 0 := σ.injective (hσ0.trans (map_zero σ).symm)
    have hv1 : v 1 = 0 := σ.injective (hσ1.trans (map_zero σ).symm)
    funext i
    fin_cases i
    · simpa using hv0
    · simpa using hv1
  · rintro rfl
    ext i
    fin_cases i <;> simp

/-- The special value of the diagonal projective map, in coordinates: the class of the pushed
vector. -/
theorem legCoordsMap_projective_coords (a b : L) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Fin 2 → K) (hv : v ≠ 0) :
    legCoordsMap_projective (σ := σ) a b ha hb (Projectivization.mk K v hv) =
      Projectivization.mk L ((legCoordsMap (σ := σ) a b) v)
        (fun h => hv ((legCoordsMap_eq_zero_iff a b ha hb v).mp h)) := by
  rw [legCoordsMap_projective, Projectivization.map_mk]

/-- The naturality square of the Legendre projective point map under base change for equal
diagonal scaling: applying the base-changed sextic map after the diagonal pushforward is the same
as applying the diagonal pushforward after the Legendre map. -/
theorem legCoordsMap_naturality_legendre [CharZero K] [CharZero L] (a : L) (ha : a ≠ 0) :
    legCoordsMap_projective (σ := σ) a a ha ha ∘ LegendreProjectiveMap =
      LegendreProjectiveMap ∘ legCoordsMap_projective (σ := σ) a a ha ha := by
  funext x
  induction x using Projectivization.ind with
  | h v hv =>
    change legCoordsMap_projective (σ := σ) a a ha ha (legImg ⟨v, hv⟩) =
      LegendreProjectiveMap
        (legCoordsMap_projective (σ := σ) a a ha ha (Projectivization.mk K v hv))
    have hne : (legCoordsMap (σ := σ) a a) v ≠ 0 :=
      fun h => hv ((legCoordsMap_eq_zero_iff a a ha ha v).mp h)
    rw [legImg_apply v hv,
      legCoordsMap_projective_coords a a ha ha ![LegendreF K v, LegendreG K v]
        (legPair_nonzero v hv),
      legCoordsMap_projective_coords a a ha ha v hv,
      LegendreProjectiveMap_coords ((legCoordsMap (σ := σ) a a) v) hne,
      legImg_apply ((legCoordsMap (σ := σ) a a) v) hne]
    refine (Projectivization.mk_eq_mk_iff L _ _ _ _).mpr
      ⟨Units.mk0 (a ^ 5)⁻¹ (inv_ne_zero (pow_ne_zero 5 ha)), ?_⟩
    change (a ^ 5)⁻¹ • ![LegendreF L ((legCoordsMap (σ := σ) a a) v),
        LegendreG L ((legCoordsMap (σ := σ) a a) v)] =
      (legCoordsMap (σ := σ) a a) ![LegendreF K v, LegendreG K v]
    rw [LegendreF_map_smul (σ := σ) a, LegendreG_map_smul (σ := σ) a]
    have hcoef : ∀ x : L, (a ^ 5)⁻¹ * (a ^ 6 * x) = a * x := by
      intro x
      have h6 : a ^ 6 = a ^ 5 * a := by ring
      calc (a ^ 5)⁻¹ * (a ^ 6 * x) = ((a ^ 5)⁻¹ * a ^ 5) * (a * x) := by rw [h6]; ring
        _ = a * x := by rw [inv_mul_cancel₀ (pow_ne_zero 5 ha), one_mul]
    ext i
    fin_cases i <;>
      simp only [Pi.smul_apply, smul_eq_mul] <;>
      exact hcoef _

/-- Base change of the Legendre projective point map along a field embedding. -/
def LegendreBaseChange (a b : L) (ha : a ≠ 0) (hb : b ≠ 0) :
    ℙ K (Fin 2 → K) → ℙ L (Fin 2 → L) :=
  legCoordsMap_projective (σ := σ) a b ha hb

/-- The Legendre projective point map commutes with base change along a field embedding for equal
diagonal scaling, in the sense that base-changing the image point is the same as base-changing the
coordinate point and then applying the sextic map. -/
theorem LegendreBaseChange_pushforward_commutes [CharZero K] [CharZero L] (a : L) (ha : a ≠ 0) :
    LegendreBaseChange (σ := σ) a a ha ha ∘ LegendreProjectiveMap =
      LegendreProjectiveMap ∘ LegendreBaseChange (σ := σ) a a ha ha :=
  legCoordsMap_naturality_legendre a ha

end BaseChange

end LeanFormal.IUT
