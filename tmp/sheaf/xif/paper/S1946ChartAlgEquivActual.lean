/-
# S1946: the actual F'-algebra chart identification of the projective closure

S1937 reduced the compactification of the actual S1726 affine model E' to a single
commutative-algebra datum, the *first missing*:

    S1937ChartAlgEquiv : (Away WGr Zbar) ≃ₐ[S1726K] S1726CoordinateRing

i.e. the degree-zero part of the homogeneous localization of the homogeneous coordinate
ring W = F'[X,Y,Z]/(Wang) at the class of Z is the affine Weierstrass coordinate ring
R' = F'[x,y]/(y^2 - (x^3 + (61/64) x^2 - (125/64) x)) of S1726, as an F'-algebra.

This file constructs that algebra isomorphism, so the datum is no longer missing.

## Construction

1. The two degree-zero classes 'XZ = X/Z' and 'YZ = Y/Z' of the chart ring.

2. *Dehomogenization* 'g : W →+* R'', X ↦ x, Y ↦ y, Z ↦ 1: the evaluation of a
   homogeneous numerator at (x,y,1).  It is well defined because Wang dehomogenizes at
   Z = 1 to the affine Weierstrass polynomial ('dehom_Wang').

3. *The inverse direction* 'psi : R' →+* Away', X ↦ X/Z, Y ↦ Y/Z, well defined for the
   same reason.

4. 'psi' is surjective: the *homogeneity identity* ('chart_fraction_eq_mk') says that for a
   homogeneous polynomial p of degree n the fraction p(X,Y,Z)/Z^n in the chart ring is the
   dehomogenization p(X/Z,Y/Z,1); every element of 'Away' is such a fraction
   ('HomogeneousLocalization.Away.mk_surjective') and every degree-n class is the class
   of a homogeneous polynomial of degree n.

5. 'psi' is injective: 'phi' (the extension of the dehomogenization 'g' to the chart ring
   via the localization at Z) is a left inverse of 'psi'.

6. Hence 'S1946ChartAlgEquiv : S1937ChartAlgEquiv', an F'-algebra isomorphism.

No 'sorry', no axiom: the only axioms are those of Mathlib's localization API
(propext, Classical.choice, Quot.sound).
-/
import tmp.sheaf.xif.paper.S1937ProjectiveClosureGeometryActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1946ChartAlgEquivActual

open MvPolynomial
open HomogeneousLocalization
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1925ProjectiveClosureActual
open LeanFormal.IUT.XiFPaper.S1937ProjectiveClosureGeometryActual

attribute [local instance] MvPolynomial.gradedAlgebra

variable [GradedRing (CohomGr (R := S1726K) Wang)]

/-! ## 1. The chart ring and its two coordinate classes -/

/-- The class of X in the homogeneous coordinate ring of the projective closure. -/
def Xbar : W := quo Wang (MvPolynomial.X 0)

theorem Xbar_mem_one : Xbar ∈ WGr 1 :=
  CohomGr_mem Wang (MvPolynomial.isHomogeneous_X (R := S1726K) 0)

/-- The class of Y in the homogeneous coordinate ring. -/
abbrev Ybar : W := S1937Ybar

theorem Ybar_mem_one : Ybar ∈ WGr 1 := S1937Ybar_mem_one

/-- 'Zbar' as an element of the power submonoid of the localization. -/
abbrev zp (n : ℕ) : Submonoid.powers Zbar := ⟨Zbar ^ n, ⟨n, rfl⟩⟩

theorem zp_coe (n : ℕ) : ((zp n : Submonoid.powers Zbar) : W) = Zbar ^ n := rfl

/-- 'X/Z', the first coordinate of the affine chart. -/
def XZ : Away WGr Zbar :=
  HomogeneousLocalization.Away.mk WGr Zbar_mem_one 1 Xbar Xbar_mem_one

/-- 'Y/Z', the second coordinate of the affine chart. -/
def YZ : Away WGr Zbar :=
  HomogeneousLocalization.Away.mk WGr Zbar_mem_one 1 Ybar Ybar_mem_one

theorem XZ_val : (algebraMap (Away WGr Zbar) (Localization.Away Zbar) XZ)
    = Localization.mk Xbar (zp 1) := by
  rw [XZ, HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]

theorem YZ_val : (algebraMap (Away WGr Zbar) (Localization.Away Zbar) YZ)
    = Localization.mk Ybar (zp 1) := by
  rw [YZ, HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]

/-- Evaluation of a trivariate polynomial at the chart point (X/Z, Y/Z, 1): the map that
sends a homogeneous numerator to its dehomogenization inside the chart ring. -/
def chartEval : MvPolynomial (Fin 3) S1726K →ₐ[S1726K] Away WGr Zbar :=
  MvPolynomial.aeval (R := S1726K) ![XZ, YZ, 1]

theorem chartEval_X (i : Fin 3) : chartEval (MvPolynomial.X i) = ![XZ, YZ, 1] i :=
  MvPolynomial.aeval_X (R := S1726K) _ i

theorem chartEval_algebraMap (c : S1726K) :
    chartEval (algebraMap S1726K (MvPolynomial (Fin 3) S1726K) c)
      = algebraMap S1726K (Away WGr Zbar) c := by
  rw [chartEval, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]

/-! ## 2. Dehomogenization at Z = 1 on the polynomial level -/

/-- Substitution X ↦ X, Y ↦ Y, Z ↦ 1 (dehomogenization at the chart Z = 1) on the
polynomial level. -/
def dehom : MvPolynomial (Fin 3) S1726K →ₐ[S1726K] MvPolynomial (Fin 2) S1726K :=
  MvPolynomial.aeval (R := S1726K) ![MvPolynomial.X 0, MvPolynomial.X 1, 1]

/-- **The homogeneous Weierstrass polynomial dehomogenizes to the affine one.**
This is the reason both chart maps are well defined. -/
theorem dehom_Wang : dehom Wang = S1726AffinePolynomial := by
  rw [S1726AffinePolynomial_eq]
  simp [dehom, Wang]
  ring

/-! ## 3. The homogeneity identity

For a homogeneous polynomial p of degree n the fraction p(X,Y,Z)/Z^n of the chart ring is
the dehomogenization p(X/Z, Y/Z, 1) of p.  This identity is what makes the chart
coordinates X/Z, Y/Z generate the chart ring; it is proved by reducing to monomials. -/

/-- Addition of fractions with the same denominator. -/
theorem mk_add_zp (a b : W) (n : ℕ) :
    Localization.mk (a + b) (zp n) = Localization.mk a (zp n) + Localization.mk b (zp n) := by
  rw [Localization.add_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
  simp only [Submonoid.coe_mul, zp_coe, one_mul]
  ring

/-- Scalar multiples of fractions. -/
theorem mk_smul_zp (c : S1726K) (a : W) (n : ℕ) :
    Localization.mk (c • a) (zp n)
      = algebraMap S1726K (Localization.Away Zbar) c * Localization.mk a (zp n) := by
  have hca : c • a = algebraMap S1726K W c * a := Algebra.smul_def c a
  rw [hca]
  have h1 : algebraMap S1726K (Localization.Away Zbar) c
      = Localization.mk (algebraMap S1726K W c) 1 := by
    rw [Localization.mk_eq_mk', IsLocalization.mk'_one,
      IsScalarTower.algebraMap_apply S1726K W (Localization.Away Zbar)]
  rw [h1, Localization.mk_mul]
  rw [show (1 : Submonoid.powers Zbar) * zp n = zp n from by ext; simp [zp]]

/-- **The monomial homogeneity identity**: X^a Y^b Z^c / Z^(a+b+c) = (X/Z)^a (Y/Z)^b. -/
theorem mk_monomial_eq (a b c : ℕ) :
    Localization.mk (Xbar ^ a * Ybar ^ b * Zbar ^ c) (zp (a + b + c))
      = Localization.mk Xbar (zp 1) ^ a * Localization.mk Ybar (zp 1) ^ b := by
  rw [Localization.mk_pow, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨zp c, ?_⟩
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, Subtype.coe_mk, zp, pow_one, pow_add]
  ring_nf

/-- Monomials of total degree n span the homogeneous polynomials of degree n. -/
theorem homogeneousSubmodule_eq_span_monomial (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) S1726K n
      = Submodule.span S1726K (Set.range (fun d : {d : Fin 3 →₀ ℕ // Finsupp.degree d = n} =>
          MvPolynomial.monomial (d : Fin 3 →₀ ℕ) 1)) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 3) S1726K n,
    AddMonoidAlgebra.supported_eq_span_single]
  congr 1
  ext x
  simp only [MvPolynomial.single_eq_monomial, Set.mem_image, Set.mem_range, Set.mem_setOf_eq,
    Subtype.exists, exists_prop]

/-- The value of a monomial inside the chart ring. -/
theorem chartEval_monomial (d : Fin 3 →₀ ℕ) :
    chartEval (MvPolynomial.monomial d 1) = XZ ^ d 0 * YZ ^ d 1 := by
  have key : chartEval (MvPolynomial.monomial d 1)
      = chartEval ((MvPolynomial.X 0 : MvPolynomial (Fin 3) S1726K) ^ d 0
          * (MvPolynomial.X 1 : MvPolynomial (Fin 3) S1726K) ^ d 1
          * (MvPolynomial.X 2 : MvPolynomial (Fin 3) S1726K) ^ d 2) := by
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    rw [Finset.prod_subset (Finset.subset_univ _)
      (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, pow_zero]), Fin.prod_univ_three]
  rw [key]
  simp only [map_mul, map_pow, chartEval_X]
  simp

/-- The value of a monomial in the homogeneous coordinate ring. -/
theorem quo_monomial_eq (d : Fin 3 →₀ ℕ) :
    quo Wang (MvPolynomial.monomial d 1) = Xbar ^ d 0 * Ybar ^ d 1 * Zbar ^ d 2 := by
  have key : quo Wang (MvPolynomial.monomial d 1)
      = quo Wang ((MvPolynomial.X 0 : MvPolynomial (Fin 3) S1726K) ^ d 0
          * (MvPolynomial.X 1 : MvPolynomial (Fin 3) S1726K) ^ d 1
          * (MvPolynomial.X 2 : MvPolynomial (Fin 3) S1726K) ^ d 2) := by
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    rw [Finset.prod_subset (Finset.subset_univ _)
      (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, pow_zero]), Fin.prod_univ_three]
  rw [key, map_mul, map_mul, map_pow, map_pow, map_pow]
  rfl

/-- The total degree of an exponent vector in three variables. -/
theorem degree_eq_sum_three (d : Fin 3 →₀ ℕ) : d.degree = d 0 + d 1 + d 2 := by
  rw [Finsupp.degree_apply,
    Finset.sum_subset (Finset.subset_univ _)
      (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi]),
    Fin.sum_univ_three]

/-- The base field action on the chart ring is compatible with the localization. -/
theorem algebraMap_away_eq (c : S1726K) :
    algebraMap (Away WGr Zbar) (Localization.Away Zbar) (algebraMap S1726K (Away WGr Zbar) c)
      = Localization.mk (algebraMap S1726K W c) 1 := by
  rw [S1937Away_algebraMap]
  rfl

/-- **The homogeneity identity.**  For a homogeneous polynomial p of degree n, the class of
p(X,Y,Z)/Z^n in the localization at Z is the dehomogenization p(X/Z, Y/Z, 1). -/
theorem chart_fraction_eq_mk (n : ℕ) (p : MvPolynomial (Fin 3) S1726K) (hp : p.IsHomogeneous n) :
    algebraMap (Away WGr Zbar) (Localization.Away Zbar) (chartEval p)
      = Localization.mk (quo Wang p) (zp n) := by
  have hspan : Submodule.span S1726K (Set.range (fun d : {d : Fin 3 →₀ ℕ // Finsupp.degree d = n} =>
      MvPolynomial.monomial (d : Fin 3 →₀ ℕ) 1))
      = MvPolynomial.homogeneousSubmodule (Fin 3) S1726K n :=
    (homogeneousSubmodule_eq_span_monomial n).symm
  have hmem : p ∈ Submodule.span S1726K
      (Set.range (fun d : {d : Fin 3 →₀ ℕ // Finsupp.degree d = n} =>
        MvPolynomial.monomial (d : Fin 3 →₀ ℕ) 1)) := by
    rw [hspan]; exact hp
  clear hp hspan
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hxd⟩ := hx
    obtain ⟨dd, hdd⟩ := d
    simp only at hxd
    subst hxd
    have hn : dd 0 + dd 1 + dd 2 = n := by
      rw [← degree_eq_sum_three]; exact hdd
    have hL : algebraMap (Away WGr Zbar) (Localization.Away Zbar) (chartEval (MvPolynomial.monomial dd 1))
        = Localization.mk Xbar (zp 1) ^ dd 0 * Localization.mk Ybar (zp 1) ^ dd 1 := by
      rw [chartEval_monomial, map_mul, map_pow, map_pow, XZ_val, YZ_val]
    have hR : Localization.mk (quo Wang (MvPolynomial.monomial dd 1)) (zp n)
        = Localization.mk Xbar (zp 1) ^ dd 0 * Localization.mk Ybar (zp 1) ^ dd 1 := by
      rw [quo_monomial_eq]
      have key := mk_monomial_eq (dd 0) (dd 1) (dd 2)
      rw [hn] at key
      exact key
    exact hL.trans hR.symm
  | zero =>
    simp only [map_zero, Localization.mk_zero]
  | add x y hx hy ihx ihy =>
    simp only [map_add, ihx, ihy, mk_add_zp]
  | smul c x hx ih =>
    have hcx : c • x = algebraMap S1726K (MvPolynomial (Fin 3) S1726K) c * x :=
      Algebra.smul_def c x
    have h1 : algebraMap S1726K (Localization.Away Zbar) c
        = Localization.mk (algebraMap S1726K W c) 1 := by
      rw [Localization.mk_eq_mk', IsLocalization.mk'_one,
        IsScalarTower.algebraMap_apply S1726K W (Localization.Away Zbar)]
    rw [hcx]
    simp only [map_mul, chartEval_algebraMap, (quo Wang).commutes c, ih, algebraMap_away_eq, h1,
      Localization.mk_mul, show (1 : Submonoid.powers Zbar) * zp n = zp n from by ext; simp [zp]]

/-- **The homogeneity identity in the chart ring**: a homogeneous class of degree n is the
fraction p(X,Y,Z)/Z^n, i.e. the dehomogenization p(X/Z, Y/Z, 1) of any homogeneous
representative. -/
theorem chartEval_eq_mk (n : ℕ) (p : MvPolynomial (Fin 3) S1726K) (hp : p.IsHomogeneous n) :
    chartEval p = HomogeneousLocalization.Away.mk WGr Zbar_mem_one n (quo Wang p)
      (by simpa using CohomGr_mem Wang hp) := by
  apply HomogeneousLocalization.val_injective
  show algebraMap (Away WGr Zbar) (Localization.Away Zbar) (chartEval p)
    = algebraMap (Away WGr Zbar) (Localization.Away Zbar)
      (HomogeneousLocalization.Away.mk WGr Zbar_mem_one n (quo Wang p) _)
  rw [chart_fraction_eq_mk n p hp, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]



/-! ## 4. The dehomogenization map 'W →+* R'' -/

/-- The class of x in the affine coordinate ring R'. -/
def xAff : S1726CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (MvPolynomial.X 0)

/-- The class of y in the affine coordinate ring R'. -/
def yAff : S1726CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (MvPolynomial.X 1)

theorem quotient_mk_aeval (p : MvPolynomial (Fin 2) S1726K) :
    MvPolynomial.aeval (R := S1726K) (fun i : Fin 2 => ![xAff, yAff] i) p
      = Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) p := by
  have h : (MvPolynomial.aeval (R := S1726K) (fun i : Fin 2 => ![xAff, yAff] i) :
        MvPolynomial (Fin 2) S1726K →ₐ[S1726K] S1726CoordinateRing)
      = Ideal.Quotient.mkₐ S1726K (Ideal.span {S1726AffinePolynomial}) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    fin_cases i <;> rfl
  rw [h, Ideal.Quotient.mkₐ_eq_mk]

theorem aeval_affine_eq_zero :
    MvPolynomial.aeval (R := S1726K) (fun i : Fin 2 => ![xAff, yAff] i) S1726AffinePolynomial
      = 0 := by
  rw [quotient_mk_aeval, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The composition of the dehomogenization of a trivariate polynomial with the
evaluation at an affine point is the evaluation of the trivariate polynomial at the
homogenized point. -/
theorem aeval_dehom {B : Type} [CommRing B] [Algebra S1726K B] (g : Fin 2 → B)
    (p : MvPolynomial (Fin 3) S1726K) :
    MvPolynomial.aeval g (dehom p)
      = MvPolynomial.aeval (R := S1726K) (fun i : Fin 3 => ![g 0, g 1, 1] i) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [dehom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    fin_cases i <;> simp [dehom]

/-- Evaluation of a trivariate polynomial at (x, y, 1) in the affine coordinate ring R'. -/
def dehomEval : MvPolynomial (Fin 3) S1726K →+* S1726CoordinateRing :=
  (MvPolynomial.aeval (R := S1726K) (fun i : Fin 3 => ![xAff, yAff, 1] i) :
    MvPolynomial (Fin 3) S1726K →ₐ[S1726K] S1726CoordinateRing)

/-- The dehomogenization of Wang at (x,y,1) vanishes in R'. -/
theorem dehomEval_Wang : dehomEval Wang = 0 := by
  have key := aeval_dehom (g := fun i : Fin 2 => ![xAff, yAff] i) Wang
  rw [dehom_Wang, aeval_affine_eq_zero] at key
  exact key.symm

/-- **Dehomogenization at Z = 1**, as a ring map out of the homogeneous coordinate ring
into the affine coordinate ring R'. -/
def dehomHom : W →+* S1726CoordinateRing :=
  Ideal.Quotient.lift (relIdeal Wang) dehomEval (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, dehomEval_Wang, zero_mul])

theorem dehomEval_quo (p : MvPolynomial (Fin 3) S1726K) :
    dehomEval p = MvPolynomial.aeval (R := S1726K) (fun i : Fin 3 => ![xAff, yAff, 1] i) p :=
  rfl

theorem dehomEval_X (i : Fin 3) : dehomEval (MvPolynomial.X i) = ![xAff, yAff, 1] i :=
  MvPolynomial.aeval_X (R := S1726K) _ i

theorem dehomHom_quo (p : MvPolynomial (Fin 3) S1726K) :
    dehomHom (quo Wang p) = dehomEval p := by
  rw [dehomHom, show quo Wang p = Ideal.Quotient.mk (relIdeal Wang) p from rfl,
    Ideal.Quotient.lift_mk]

/-- The dehomogenization sends Z to 1: Z = 1 is the affine chart. -/
theorem dehomHom_Zbar : dehomHom Zbar = 1 := by
  rw [show Zbar = quo Wang (MvPolynomial.X 2) from rfl, dehomHom_quo, dehomEval_X]
  rfl

/-! ## 5. The chart map 'Away →+* R'' out of the localization at Z -/

/-- **The dehomogenization of the chart ring**: the extension of 'dehomHom' to the
localization at Z, which sends Z to the unit 1. -/
def phi : Away WGr Zbar →+* S1726CoordinateRing :=
  (Localization.awayLift dehomHom Zbar (by rw [dehomHom_Zbar]; exact isUnit_one)).comp
    (algebraMap (Away WGr Zbar) (Localization.Away Zbar))

theorem phi_apply (y : Away WGr Zbar) :
    phi y = Localization.awayLift dehomHom Zbar (by rw [dehomHom_Zbar]; exact isUnit_one)
      (algebraMap (Away WGr Zbar) (Localization.Away Zbar) y) := rfl

/-- The value of the chart map on a homogeneous fraction. -/
theorem phi_mk {n : ℕ} {a : W} (ha : a ∈ WGr n) :
    phi (HomogeneousLocalization.Away.mk WGr Zbar_mem_one n a (by simpa using ha))
      = dehomHom a := by
  rw [phi_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have hv : dehomHom Zbar * (1 : S1726CoordinateRing) = 1 := by rw [dehomHom_Zbar, one_mul]
  rw [Localization.awayLift_mk dehomHom Zbar a 1 hv n, one_pow, mul_one]

/-- The chart map sends X/Z to x. -/
theorem phi_XZ : phi XZ = xAff := by
  rw [XZ, phi_mk Xbar_mem_one,
    show dehomHom Xbar = dehomEval (MvPolynomial.X 0) from dehomHom_quo _]
  rw [dehomEval_X]
  rfl

/-- The chart map sends Y/Z to y. -/
theorem phi_YZ : phi YZ = yAff := by
  rw [YZ, phi_mk Ybar_mem_one,
    show dehomHom Ybar = dehomEval (MvPolynomial.X 1) from dehomHom_quo _]
  rw [dehomEval_X]
  rfl


/-! ## 6. The chart fraction map 'R' →+* Away' -/

/-- Evaluation of a bivariate polynomial at the chart coordinates X/Z, Y/Z. -/
def chartEval2 : MvPolynomial (Fin 2) S1726K →ₐ[S1726K] Away WGr Zbar :=
  MvPolynomial.aeval (R := S1726K) ![XZ, YZ]

theorem chartEval2_X (i : Fin 2) : chartEval2 (MvPolynomial.X i) = ![XZ, YZ] i :=
  MvPolynomial.aeval_X (R := S1726K) _ i

theorem chartEval2_algebraMap (c : S1726K) :
    chartEval2 (algebraMap S1726K (MvPolynomial (Fin 2) S1726K) c)
      = algebraMap S1726K (Away WGr Zbar) c := by
  rw [chartEval2, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]

/-- Dehomogenization at Z = 1 commutes with the evaluation at the chart point. -/
theorem chartEval2_dehom (p : MvPolynomial (Fin 3) S1726K) :
    chartEval2 (dehom p) = chartEval p :=
  aeval_dehom (g := fun i : Fin 2 => ![XZ, YZ] i) p

/-- The affine Weierstrass polynomial vanishes at the chart coordinates. -/
theorem quo_Wang_eq_zero : quo Wang Wang = 0 := by
  rw [show quo Wang Wang = Ideal.Quotient.mk (relIdeal Wang) Wang from rfl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem chartEval2_affinePolynomial : chartEval2 S1726AffinePolynomial = 0 := by
  rw [← dehom_Wang, chartEval2_dehom]
  apply HomogeneousLocalization.val_injective
  show algebraMap (Away WGr Zbar) (Localization.Away Zbar) (chartEval Wang)
    = algebraMap (Away WGr Zbar) (Localization.Away Zbar) (0 : Away WGr Zbar)
  rw [chart_fraction_eq_mk 3 Wang Wang_isHomogeneous, quo_Wang_eq_zero, map_zero]
  exact Localization.mk_zero _

/-- **The chart fraction map** 'R' →+* Away' sending x to X/Z and y to Y/Z. -/
def psi : S1726CoordinateRing →ₐ[S1726K] Away WGr Zbar :=
  Ideal.Quotient.liftₐ (Ideal.span {S1726AffinePolynomial}) chartEval2 (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, chartEval2_affinePolynomial, zero_mul])

theorem psi_mk (p : MvPolynomial (Fin 2) S1726K) :
    psi (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) p) = chartEval2 p := by
  rw [psi, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

/-! ## 7. The two chart maps are mutually inverse -/

theorem phi_algebraMap (c : S1726K) :
    phi (algebraMap S1726K (Away WGr Zbar) c)
      = algebraMap S1726K S1726CoordinateRing c := by
  rw [phi_apply, algebraMap_away_eq]
  have hv : dehomHom Zbar * (1 : S1726CoordinateRing) = 1 := by rw [dehomHom_Zbar, one_mul]
  rw [show (1 : Submonoid.powers Zbar) = ⟨Zbar ^ 0, ⟨0, rfl⟩⟩ from Subtype.ext (by simp)]
  rw [Localization.awayLift_mk dehomHom Zbar (algebraMap S1726K W c) 1 hv 0, pow_zero, mul_one]
  rw [← (quo Wang).commutes c, MvPolynomial.algebraMap_eq, dehomHom_quo]
  exact MvPolynomial.aeval_C (R := S1726K) _ c

theorem phi_vec (i : Fin 2) : phi (![XZ, YZ] i) = ![xAff, yAff] i := by
  fin_cases i
  · show phi XZ = xAff
    exact phi_XZ
  · show phi YZ = yAff
    exact phi_YZ

/-- The dehomogenization of the chart ring inverts the chart fraction map. -/
theorem phi_chartEval2 (p : MvPolynomial (Fin 2) S1726K) :
    phi (chartEval2 p)
      = MvPolynomial.aeval (R := S1726K) (fun i : Fin 2 => ![xAff, yAff] i) p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show (MvPolynomial.C c : MvPolynomial (Fin 2) S1726K)
        = algebraMap S1726K (MvPolynomial (Fin 2) S1726K) c from rfl,
      chartEval2_algebraMap, phi_algebraMap]
    exact (MvPolynomial.aeval_C (R := S1726K) _ c).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, chartEval2_X, MvPolynomial.aeval_X, phi_vec i]

/-- **The dehomogenization of the chart ring is a left inverse of the chart fraction
map.** -/
theorem phi_comp_psi : phi.comp psi.toRingHom = RingHom.id S1726CoordinateRing := by
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun p => ?_
  show phi (psi (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) p))
    = Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) p
  rw [psi_mk, phi_chartEval2, quotient_mk_aeval]

/-! ## 8. The chart fraction map is surjective -/



theorem psi_surjective : Function.Surjective psi := by
  intro y
  obtain ⟨n, a, ha, hx⟩ :=
    HomogeneousLocalization.Away.mk_surjective WGr Zbar_mem_one y
  have ha' : a ∈ WGr n := by simpa using ha
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha'
  refine ⟨Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (dehom p), ?_⟩
  rw [psi_mk, chartEval2_dehom, ← hx]
  exact chartEval_eq_mk n p hp

theorem phi_psi (r : S1726CoordinateRing) : phi (psi r) = r := by
  have h := congrArg (fun f : S1726CoordinateRing →+* S1726CoordinateRing => f r) phi_comp_psi
  simpa using h

theorem psi_injective : Function.Injective psi := by
  intro r s h
  calc r = phi (psi r) := (phi_psi r).symm
    _ = phi (psi s) := by rw [h]
    _ = s := phi_psi s

theorem psi_bijective : Function.Bijective psi :=
  ⟨psi_injective, psi_surjective⟩

/-! ## 9. The F'-algebra chart identification -/

/-- The ring isomorphism between the chart ring and the affine coordinate ring. -/
noncomputable def chartRingEquiv : S1726CoordinateRing ≃+* Away WGr Zbar where
  toFun := psi
  invFun := phi
  left_inv := phi_psi
  right_inv := fun y => by
    obtain ⟨r, rfl⟩ := psi_surjective y
    rw [phi_psi]
  map_mul' := psi.map_mul
  map_add' := psi.map_add

/-- **The chart identification of S1937**: the degree-zero part of the homogeneous
localization of the homogeneous coordinate ring at Z is the affine Weierstrass coordinate
ring of S1726, as an F'-algebra. -/
noncomputable def chartAlgEquiv : Away WGr Zbar ≃ₐ[S1726K] S1726CoordinateRing :=
  AlgEquiv.ofRingEquiv (f := chartRingEquiv.symm) (by
    intro c
    show chartRingEquiv.symm (algebraMap S1726K (Away WGr Zbar) c)
      = algebraMap S1726K S1726CoordinateRing c
    have h : chartRingEquiv (algebraMap S1726K S1726CoordinateRing c)
        = algebraMap S1726K (Away WGr Zbar) c := psi.commutes c
    rw [← h]
    exact chartRingEquiv.symm_apply_apply _)

/-- **The first missing datum of S1937 is no longer missing.** -/
noncomputable def S1946ChartAlgEquiv : S1937ChartAlgEquiv := chartAlgEquiv


/-! ## 10. The chart identification does what it should -/

/-- The chart identification sends X/Z to the affine coordinate x. -/
theorem S1946ChartAlgEquiv_XZ : S1946ChartAlgEquiv XZ = xAff := by
  show chartRingEquiv.symm XZ = xAff
  rw [RingEquiv.symm_apply_eq]
  show XZ = psi xAff
  rw [show xAff = Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (MvPolynomial.X 0)
      from rfl, psi_mk, chartEval2_X]
  rfl

/-- The chart identification sends Y/Z to the affine coordinate y. -/
theorem S1946ChartAlgEquiv_YZ : S1946ChartAlgEquiv YZ = yAff := by
  show chartRingEquiv.symm YZ = yAff
  rw [RingEquiv.symm_apply_eq]
  show YZ = psi yAff
  rw [show yAff = Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (MvPolynomial.X 1)
      from rfl, psi_mk, chartEval2_X]
  rfl

/-- The ring-valued chart residual of S1925 is filled by the algebra chart identification. -/
noncomputable def S1946ChartIso : S1925ChartIso :=
  S1937ChartIso_of_alg S1946ChartAlgEquiv

theorem S1946ChartIso_apply (y : Away WGr Zbar) : S1946ChartIso y = S1946ChartAlgEquiv y := rfl

/-- **Consumer**: with the chart identification in place and the density of the affine
chart, S1937 produces the scheme-level compactification datum of the actual affine model of
E' over F' (projective closure, point at infinity, separation, density, properness). -/
noncomputable def S1946AffineCompactification (hdense : S1925DenseChart) :=
  S1937AffineCompactification S1946ChartAlgEquiv hdense

/-- **The scheme-level compactification of the actual S1726 affine model** from the single
remaining algebraic hypothesis that the homogeneous coordinate ring is a domain (i.e. that
Wang is irreducible), which is exactly the density residual of S1937. -/
noncomputable def S1946Compactification_of_domain (hdom : IsDomain W) :=
  S1946AffineCompactification (S1937DenseChart_of_domain hdom)

/-! ## 11. Axiom audit -/

#print axioms chart_fraction_eq_mk
#print axioms chartEval_eq_mk
#print axioms chartEval2_affinePolynomial
#print axioms phi_comp_psi
#print axioms psi_surjective
#print axioms psi_bijective
#print axioms chartRingEquiv
#print axioms chartAlgEquiv
#print axioms S1946ChartAlgEquiv
#print axioms S1946ChartAlgEquiv_XZ
#print axioms S1946ChartAlgEquiv_YZ
#print axioms S1946ChartIso
#print axioms S1946AffineCompactification
#print axioms S1946Compactification_of_domain

end LeanFormal.IUT.XiFPaper.S1946ChartAlgEquivActual