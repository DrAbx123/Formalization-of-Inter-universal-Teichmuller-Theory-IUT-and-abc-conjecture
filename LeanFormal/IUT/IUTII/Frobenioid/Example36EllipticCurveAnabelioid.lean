import LeanFormal.IUT.IUTII.Frobenioid.Example36EtalePiOneKernelRealization
import LeanFormal.IUT.ABCBridge.Galois.EllipticPrimeTorsionGalois
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Iut.Foundations.Orbicurve

/-!
# Concrete elliptic-curve anabelioid: the mod-two Tate module as geometric kernel

Source anchor: IUT II, Sections 3-6, boundary item (1) of the prime-strip
Frobenioid category contract (the geometric fundamental group of the base
curve); consumers IUT III, Proposition 3.5 / Theorem 3.11(ii), and the
vertical log-Kummer / K1-K2 input chain.  The preceding reduced module
Example36EtalePiOneKernelRealization.lean realized the exact-sequence shape
with a *named reduced kernel model* Z/2.  This module replaces that reduced
model by a concrete arithmetic-geometric finite-level Tate-module group of a
concrete elliptic curve available in the tree.

## The concrete curve and its level-two Tate module

The curve is the concrete Weierstrass curve

  curveY2EqX3SubX : WeierstrassCurve Q,  y^2 = x^3 - x,

with discriminant 64, hence an elliptic curve (curveY2EqX3SubX_isElliptic).
Over the separable closure of Q (tateGeometricBase = SeparableClosure Q) the
actual 2-torsion subgroup

  tateLevelTwoTorsion = torsionSubgroup (curveY2EqX3SubX / tateGeometricBase) 2

is the mod-two Tate-module carrier, built with the existing division-point
API (LeanFormal.IUT.ABCBridge.Galois.EllipticPrimeTorsionGalois and
EllipticDivisionPolynomialEvaluation).  The file proves unconditionally:

* the 2-torsion criterion y-coordinate zero lemma twoTorsion_y_eq_zero, via
  Mathlib's psi_2 = 2Y + a_1 X + a_3 and the repo lemma
  two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero;
* the x-coordinate equation x^3 - x = 0 for 2-torsion points with y = 0, and
  the root classification cube_sub_eq_zero_iff;
* that every element of tateLevelTwoTorsion is one of the four explicit points
  0, (0,0), (1,0), (-1,0) (tateLevelTwoFourPoints_surjective), hence
  tateLevelTwoTorsion is finite;
* nontriviality: the concrete point (0,0) over Q is nonzero and 2-torsion
  (rationalTwoTorsionPoint_ne_zero, rationalTwoTorsionPoint_two_nsmul), and
  its separable-closure version tateLevelTwoPointZeroZero is a nonzero element
  of tateLevelTwoTorsion;
* the concrete distinctness of (0,0), (1,0), (-1,0) and 0, so the level-two
  Tate module is not cyclic of order two (tateLevelTwoTorsion_not_mulEquiv_zmod_two).

The level-two Tate module is made into a profinite group
tateLevelTwoProfiniteGroup by viewing the finite group as a discrete profinite
group (tateLevelTwoProfiniteGroup_coe).

## The actual Galois action

The actual Galois action of the absolute Galois group of Q on E[2] is
tateLevelTwoGaloisAction, obtained from the existing
galoisTorsionEquiv of the division-point API.  The file records its identity
law (tateLevelTwoGaloisAction_one), its composition law
(tateLevelTwoGaloisAction_mul) and its ZMod 2-linearity
(tateLevelTwoGaloisAction_zmod_smul).  The absolute Galois group of Q is the
profinite group rationalAbsoluteGaloisGroup = Iut.AbsoluteGaloisProfinite Q,
whose underlying type is exactly the automorphism group of the separable
closure that acts on E[2] (rationalAbsoluteGaloisGroup_coe).

## Anabelioid realization and the D-prime-strip

The finite-level total group is the product
tateLevelTwoAnabelioidTotalGroup = Gal(Qbar/Q) x E[2], a genuine product of
profinite groups with the genuine continuous first projection
tateLevelTwoAnabelioidProjection.  The associated anabelioids are

* tateLevelTwoAnabelioid = B(E[2]),
* rationalAbsoluteGaloisAnabelioid = B(Gal(Qbar/Q)),
* tateLevelTwoAnabelioidTotal = B(Gal(Qbar/Q) x E[2]),

built with Iut.continuousActionEtaleFundamentalGroup, and the pointed
anabelioid morphism tateLevelTwoAnabelioidMorphism is induced by the
projection via Iut.continuousActionPointedHom.  The induced map on certified
fundamental groups is proved to be the projection itself.

The single-place D-prime-strip ellipticCurveAnabelioidDPrimeStrip has Pi equal
to the certified fundamental group of B(Gal x E[2]) and G equal to the
certified fundamental group of B(Gal).  Its geometric kernel is proved equal
to the kernel of the genuine projection
(ellipticCurveAnabelioidDPrimeStrip_geometric_eq_projectionKernel), hence
multiplicatively equivalent to the concrete level-two Tate module E[2]
(ellipticCurveAnabelioidDPrimeStrip_geometricMulEquiv).  The kernel is
nontrivial (an explicit nontrivial element is produced), so the strip has a
nontrivial geometric kernel, and the kernel is not the reduced Z/2 model of
the preceding file (ellipticCurveAnabelioidDPrimeStrip_geometric_not_zmodTwo).

## Honest boundary: what is NOT proved here

This is the *mod-2 finite level*, not the pro-2 Tate module and not the full
geometric fundamental group of the curve.  The exact missing source
constructions are:

(1) The projective system E[2^(n+1)] -> E[2^n] given by multiplication by 2
    and its inverse limit T_2(E) = lim_n E[2^n] as a profinite Galois module.
    Mathlib 4.32.2 provides only the single-level torsion subgroup; it has no
    transition maps between E[2^(n+1)] and E[2^n], no projective limit of
    finite Galois modules, and (in the repo) the nsmul torsion criterion
    n • P = 0 ↔ psi_n(P) = 0 is available only for n = 2 (the general odd-n
    bridge DivisionPolynomialDetectsTorsion is a named interface, not a
    theorem).
(2) The continuous action of Gal(Qbar/Q) on the projective limit T_2(E), and
    the identification of the finite-level action with the reduction of the
    continuous pro-2 representation.  The file proves the mod-2 action laws
    only as an abstract action of the automorphism group; continuity with
    respect to the Krull topology is not formalized here.  (The separate
    PuncturedEllipticCurve.LTorsion API of
    Foundations/Geometry/EllipticTorsion.lean does prove continuity of the
    matrix representation for l >= 5 given a rank-two basis; that is a
    different, higher-level API and is not used here.)
(3) The source curve object itself: the whole nonabelian etale fundamental
    group of the ONCE-PUNCTURED curve X = (y^2 = x^3 - x, removed origin)
    over Q, its arithmetic projection to Gal(Qbar/Q), and its geometric
    kernel.  The geometric kernel of the proper elliptic curve is the FULL
    Tate module prod_l T_l(E) (product over all primes l); T_2(E) is only
    the pro-2 factor/quotient.  In particular the future target is NOT the
    sequence 1 -> T_2(E) -> pi_1^et(E) -> Gal(Qbar/Q) -> 1.  The corrected
    frozen card is
    LeanFormal/IUT/IUTII/Frobenioid/Example36EllipticCurveSourcePiCard.lean
    (SourceCurvePiData / SourceFullTateModuleData); this mod-2 file realizes
    only the direct product Gal(Qbar/Q) x E[2], a finite-level split product
    model, not the curve anabelioid.  The card is not proved and has no
    consumer here.
(4) The rank-two basis E[l] ~= (Z/l)^2 (repo obligation
    Foundations.Geometry.elliptic-l-torsion-rank-two, status pending) and any
    large-image statement.  Neither is used or claimed here.

Consequently boundary item (1) of the prime-strip contract is NOT discharged
by this file: the geometric kernel realized here is the concrete mod-two
finite abelian layer of a concrete elliptic curve, not the geometric
fundamental group of the once-punctured curve, and the source Pi, the full
Tate module and the pro-2 limit remain frozen cards (see
Example36EllipticCurveSourcePiCard.lean).  No theta / q-pilot / Tate
identification and no arithmetic degree or log-volume claim is made.

## Reused files

* LeanFormal/IUT/IUTII/Frobenioid/Example36EtalePiOneKernelRealization.lean:
  profiniteProduct, profiniteProductFst, prodFstKerMulEquiv,
  reducedGeometricKernelModel, HasNontrivialGeometricKernel, the anabelioid
  D-prime-strip pattern.
* LeanFormal/IUT/ABCBridge/Galois/EllipticPrimeTorsionGalois.lean:
  torsionSubgroup, galoisTorsionEquiv and its action laws.
* LeanFormal/IUT/ABCBridge/Galois/EllipticDivisionPolynomialEvaluation.lean:
  evalDivisionPolynomial, two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero.
* Iut/Foundations/Orbicurve.lean: AbsoluteGaloisProfinite.
* Iut/Foundations/SourceContinuousAnabelioid.lean (transitively): the certified
  anabelioid B(G) and pointed anabelioid morphisms.
* Mathlib: WeierstrassCurve.IsElliptic, the affine point group law
  (Point.some, Point.add_self_of_Y_eq, Point.some_ne_zero, Point.some.injEq),
  ProfiniteGrp.ofFiniteGrp.
-/

open WeierstrassCurve
open scoped WeierstrassCurve

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

/-! ## Concrete elliptic curve -/

/-- The concrete Weierstrass curve y^2 = x^3 - x over Q. -/
def curveY2EqX3SubX : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -1
  a₆ := 0

/-- The curve y^2 = x^3 - x is an elliptic curve (discriminant 64). -/
instance curveY2EqX3SubX_isElliptic : curveY2EqX3SubX.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curveY2EqX3SubX, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The point (0,0) of y^2 = x^3 - x is nonsingular over Q. -/
theorem rationalTwoTorsionNonsingular :
    curveY2EqX3SubX.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  constructor <;> norm_num [curveY2EqX3SubX]

/-- The rational point (0,0) of y^2 = x^3 - x. -/
def rationalTwoTorsionPoint : curveY2EqX3SubX.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some 0 0 rationalTwoTorsionNonsingular

/-- The rational point (0,0) is 2-torsion. -/
theorem rationalTwoTorsionPoint_two_nsmul :
    (2 : ℕ) • rationalTwoTorsionPoint = 0 := by
  change (2 : ℕ) •
    WeierstrassCurve.Affine.Point.some 0 0 rationalTwoTorsionNonsingular = 0
  rw [WeierstrassCurve.two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero,
    WeierstrassCurve.evalDivisionPolynomial_two]
  norm_num [curveY2EqX3SubX]

/-- The rational point (0,0) is nonzero. -/
theorem rationalTwoTorsionPoint_ne_zero : rationalTwoTorsionPoint ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero rationalTwoTorsionNonsingular

/-! ## The finite-level Tate module at level two over the separable closure -/

/-- The separable closure of Q, used as the geometric base field. -/
abbrev tateGeometricBase : Type := SeparableClosure ℚ

local instance : DecidableEq tateGeometricBase := Classical.decEq tateGeometricBase

/-- The coefficients of the base-changed curve over the separable closure. -/
theorem tateCurveCoefficients :
    (curveY2EqX3SubX⁄tateGeometricBase).a₁ = 0 ∧
      (curveY2EqX3SubX⁄tateGeometricBase).a₂ = 0 ∧
      (curveY2EqX3SubX⁄tateGeometricBase).a₃ = 0 ∧
      (curveY2EqX3SubX⁄tateGeometricBase).a₄ = -1 ∧
      (curveY2EqX3SubX⁄tateGeometricBase).a₆ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [WeierstrassCurve.baseChange, curveY2EqX3SubX]

theorem tateNonsingularZeroZero :
    (curveY2EqX3SubX⁄tateGeometricBase).toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  obtain ⟨-, -, -, -, ha6⟩ := tateCurveCoefficients
  obtain ⟨-, -, ha3, ha4, -⟩ := tateCurveCoefficients
  exact ⟨ha6, Or.inr (by rw [ha4]; norm_num)⟩

theorem tateNonsingularOneZero :
    (curveY2EqX3SubX⁄tateGeometricBase).toAffine.Nonsingular 1 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff']
    obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := tateCurveCoefficients
    rw [ha1, ha2, ha3, ha4, ha6]
    norm_num
  · obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := tateCurveCoefficients
    rw [ha1, ha2, ha3, ha4]
    left
    norm_num

theorem tateNonsingularMinusOneZero :
    (curveY2EqX3SubX⁄tateGeometricBase).toAffine.Nonsingular (-1) 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff']
    obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := tateCurveCoefficients
    rw [ha1, ha2, ha3, ha4, ha6]
    norm_num
  · obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := tateCurveCoefficients
    rw [ha1, ha2, ha3, ha4]
    left
    norm_num

/-- The level-two Tate module, as the actual 2-torsion subgroup of the curve over
the separable closure. -/
noncomputable abbrev tateLevelTwoTorsion :
    AddSubgroup (WeierstrassCurve.Affine.Point
      (curveY2EqX3SubX⁄tateGeometricBase)) :=
  LeanFormal.IUT.ABCBridge.Galois.torsionSubgroup
    (curveY2EqX3SubX⁄tateGeometricBase) 2

theorem tateLevelTwo_mem_iff {P : WeierstrassCurve.Affine.Point
    (curveY2EqX3SubX⁄tateGeometricBase)} :
    P ∈ tateLevelTwoTorsion ↔ (2 : ℕ) • P = 0 :=
  LeanFormal.IUT.ABCBridge.Galois.mem_torsionSubgroup

/-- A point of the form (x, 0) on y^2 = x^3 - x is 2-torsion. -/
theorem two_nsmul_some_y_zero {x : tateGeometricBase}
    (h : (curveY2EqX3SubX⁄tateGeometricBase).toAffine.Nonsingular x 0) :
    (2 : ℕ) • WeierstrassCurve.Affine.Point.some x 0 h = 0 := by
  rw [WeierstrassCurve.two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero,
    WeierstrassCurve.evalDivisionPolynomial_two]
  obtain ⟨ha1, -, ha3, -, -⟩ := tateCurveCoefficients
  rw [ha1, ha3]
  ring

/-- The four concrete elements of the level-two Tate module: 0, (0,0), (1,0), (-1,0). -/
noncomputable def tateLevelTwoFourPoints : Fin 4 → tateLevelTwoTorsion
  | ⟨0, _⟩ => ⟨0, by rw [tateLevelTwo_mem_iff]; exact nsmul_zero 2⟩
  | ⟨1, _⟩ => ⟨WeierstrassCurve.Affine.Point.some 0 0 tateNonsingularZeroZero,
      by rw [tateLevelTwo_mem_iff]; exact two_nsmul_some_y_zero tateNonsingularZeroZero⟩
  | ⟨2, _⟩ => ⟨WeierstrassCurve.Affine.Point.some 1 0 tateNonsingularOneZero,
      by rw [tateLevelTwo_mem_iff]; exact two_nsmul_some_y_zero tateNonsingularOneZero⟩
  | ⟨3, _⟩ => ⟨WeierstrassCurve.Affine.Point.some (-1) 0 tateNonsingularMinusOneZero,
      by rw [tateLevelTwo_mem_iff]; exact two_nsmul_some_y_zero tateNonsingularMinusOneZero⟩
  | ⟨n + 4, hn⟩ => absurd hn (by omega)

/-- The two-torsion point (x, y) over the separable closure has y = 0. -/
theorem twoTorsion_y_eq_zero {x y : tateGeometricBase}
    {h : (curveY2EqX3SubX⁄tateGeometricBase).toAffine.Nonsingular x y}
    (h2 : (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y h = 0) : y = 0 := by
  rw [WeierstrassCurve.two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero] at h2
  rw [WeierstrassCurve.evalDivisionPolynomial_two] at h2
  obtain ⟨ha1, -, ha3, -, -⟩ := tateCurveCoefficients
  rw [ha1, ha3, zero_mul, add_zero] at h2
  have h2' : (2 : tateGeometricBase) * y = 0 := by simpa using h2
  haveI : CharZero tateGeometricBase := charZero_of_injective_algebraMap
    (algebraMap ℚ tateGeometricBase).injective
  exact (mul_eq_zero.mp h2').resolve_left (by norm_num)

/-- The x-coordinate of a two-torsion point with y = 0 is a root of x^3 - x. -/
theorem twoTorsion_equation {x : tateGeometricBase}
    {h : (curveY2EqX3SubX⁄tateGeometricBase).toAffine.Nonsingular x 0} :
    x ^ 3 - x = 0 := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff'] at heq
  obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := tateCurveCoefficients
  rw [ha1, ha2, ha3, ha4, ha6] at heq
  ring_nf at heq
  linear_combination -heq

/-- The roots of x^3 - x over the separable closure are 0, 1, -1. -/
theorem cube_sub_eq_zero_iff (x : tateGeometricBase) :
    x ^ 3 - x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1 := by
  have hfac : x ^ 3 - x = x * (x - 1) * (x + 1) := by ring
  rw [hfac]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h0 | h1'
      · exact Or.inl h0
      · exact Or.inr (Or.inl (sub_eq_zero.mp h1'))
    · exact Or.inr (Or.inr (by linear_combination h2))
  · rintro (h0 | h1 | hm1)
    · rw [h0]; ring
    · rw [h1]; ring
    · rw [hm1]; ring

theorem tateLevelTwoFourPoints_surjective :
    Function.Surjective tateLevelTwoFourPoints := by
  rintro ⟨P, hP⟩
  rw [tateLevelTwo_mem_iff] at hP
  cases P with
  | zero =>
      exact ⟨0, Subtype.ext rfl⟩
  | some x y h =>
      have hy : y = 0 := twoTorsion_y_eq_zero hP
      have h0 : (curveY2EqX3SubX⁄tateGeometricBase).toAffine.Nonsingular x 0 := hy ▸ h
      have hsub : (⟨WeierstrassCurve.Affine.Point.some x y h, hP⟩ : tateLevelTwoTorsion) =
          ⟨WeierstrassCurve.Affine.Point.some x 0 h0,
            (tateLevelTwo_mem_iff).mpr (by
              rw [show WeierstrassCurve.Affine.Point.some x 0 h0 =
                  WeierstrassCurve.Affine.Point.some x y h from
                (WeierstrassCurve.Affine.Point.some.injEq x 0 h0 x y h).mpr ⟨rfl, hy.symm⟩]
              exact hP)⟩ :=
        Subtype.ext ((WeierstrassCurve.Affine.Point.some.injEq x y h x 0 h0).mpr ⟨rfl, hy⟩)
      rw [hsub]
      have hP0 : (2 : ℕ) • WeierstrassCurve.Affine.Point.some x 0 h0 = 0 := by
        rw [show WeierstrassCurve.Affine.Point.some x 0 h0 =
            WeierstrassCurve.Affine.Point.some x y h from
          (WeierstrassCurve.Affine.Point.some.injEq x 0 h0 x y h).mpr ⟨rfl, hy.symm⟩]
        exact hP
      have hx : x ^ 3 - x = 0 := twoTorsion_equation (h := h0)
      rcases (cube_sub_eq_zero_iff x).mp hx with hx0 | hx1 | hxm1
      · refine ⟨1, ?_⟩
        apply Subtype.ext
        exact (WeierstrassCurve.Affine.Point.some.injEq 0 0 tateNonsingularZeroZero x 0 h0).mpr
          ⟨hx0.symm, rfl⟩
      · refine ⟨2, ?_⟩
        apply Subtype.ext
        exact (WeierstrassCurve.Affine.Point.some.injEq 1 0 tateNonsingularOneZero x 0 h0).mpr
          ⟨hx1.symm, rfl⟩
      · refine ⟨3, ?_⟩
        apply Subtype.ext
        exact (WeierstrassCurve.Affine.Point.some.injEq (-1) 0
          tateNonsingularMinusOneZero x 0 h0).mpr
          ⟨hxm1.symm, rfl⟩

/-- The level-two Tate module is finite. -/
noncomputable instance tateLevelTwoFintype : Fintype tateLevelTwoTorsion :=
  Fintype.ofSurjective tateLevelTwoFourPoints tateLevelTwoFourPoints_surjective


/-! ## The profinite level-two Tate module -/

/-- The level-two Tate module as a profinite group (finite discrete). -/
noncomputable abbrev tateLevelTwoProfiniteGroup : ProfiniteGrp :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative tateLevelTwoTorsion))

theorem tateLevelTwoProfiniteGroup_coe :
    (tateLevelTwoProfiniteGroup : Type) = Multiplicative tateLevelTwoTorsion :=
  rfl

/-- The nonzero two-torsion point (0,0) as an element of the level-two Tate module. -/
noncomputable def tateLevelTwoPointZeroZero : tateLevelTwoTorsion :=
  ⟨WeierstrassCurve.Affine.Point.some 0 0 tateNonsingularZeroZero,
    (tateLevelTwo_mem_iff).mpr (two_nsmul_some_y_zero tateNonsingularZeroZero)⟩

/-- The point (1,0) as an element of the level-two Tate module. -/
noncomputable def tateLevelTwoPointOneZero : tateLevelTwoTorsion :=
  ⟨WeierstrassCurve.Affine.Point.some 1 0 tateNonsingularOneZero,
    (tateLevelTwo_mem_iff).mpr (two_nsmul_some_y_zero tateNonsingularOneZero)⟩

/-- The point (-1,0) as an element of the level-two Tate module. -/
noncomputable def tateLevelTwoPointMinusOneZero : tateLevelTwoTorsion :=
  ⟨WeierstrassCurve.Affine.Point.some (-1) 0 tateNonsingularMinusOneZero,
    (tateLevelTwo_mem_iff).mpr (two_nsmul_some_y_zero tateNonsingularMinusOneZero)⟩

theorem tateLevelTwoPointZeroZero_ne_zero : tateLevelTwoPointZeroZero ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  exact WeierstrassCurve.Affine.Point.some_ne_zero tateNonsingularZeroZero h'

theorem tateLevelTwoPointOneZero_ne_zero : tateLevelTwoPointOneZero ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  exact WeierstrassCurve.Affine.Point.some_ne_zero tateNonsingularOneZero h'

theorem tateLevelTwoPointMinusOneZero_ne_zero : tateLevelTwoPointMinusOneZero ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  exact WeierstrassCurve.Affine.Point.some_ne_zero tateNonsingularMinusOneZero h'

theorem tateLevelTwoPointZeroZero_ne_oneZero :
    tateLevelTwoPointZeroZero ≠ tateLevelTwoPointOneZero := by
  intro h
  have h' := congrArg Subtype.val h
  have hcoords := (WeierstrassCurve.Affine.Point.some.injEq 0 0 tateNonsingularZeroZero
    1 0 tateNonsingularOneZero).mp h'
  norm_num at hcoords

theorem tateLevelTwoPointZeroZero_ne_minusOneZero :
    tateLevelTwoPointZeroZero ≠ tateLevelTwoPointMinusOneZero := by
  intro h
  have h' := congrArg Subtype.val h
  have hcoords := (WeierstrassCurve.Affine.Point.some.injEq 0 0 tateNonsingularZeroZero
    (-1) 0 tateNonsingularMinusOneZero).mp h'
  norm_num at hcoords

/-- The level-two Tate module has a nontrivial element. -/
theorem tateLevelTwoTorsion_exists_ne_zero :
    ∃ x : tateLevelTwoTorsion, x ≠ 0 :=
  ⟨tateLevelTwoPointZeroZero, tateLevelTwoPointZeroZero_ne_zero⟩

/-- The profinite level-two Tate module has an element distinct from the identity. -/
theorem tateLevelTwoProfiniteGroup_exists_ne_one :
    ∃ x : (tateLevelTwoProfiniteGroup : Type), x ≠ 1 :=
  ⟨Multiplicative.ofAdd tateLevelTwoPointZeroZero, fun h =>
    tateLevelTwoPointZeroZero_ne_zero (congrArg Multiplicative.toAdd h)⟩

theorem tateLevelTwoProfiniteGroup_nontrivial :
    Nontrivial (tateLevelTwoProfiniteGroup : Type) :=
  let ⟨x, hx⟩ := tateLevelTwoProfiniteGroup_exists_ne_one
  ⟨x, 1, hx⟩

/-! ## The actual Galois action on the level-two Tate module -/

/-- The actual Galois action of the absolute Galois group of Q on the level-two
Tate module E[2] of y^2 = x^3 - x. -/
noncomputable def tateLevelTwoGaloisAction
    (σ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) :
    tateLevelTwoTorsion ≃+ tateLevelTwoTorsion :=
  LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv curveY2EqX3SubX 2 σ

/-- The identity Galois element acts trivially. -/
theorem tateLevelTwoGaloisAction_one :
    tateLevelTwoGaloisAction 1 = AddEquiv.refl tateLevelTwoTorsion := by
  ext P
  exact congrArg Subtype.val
    (LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_one_apply curveY2EqX3SubX 2 P)

/-- The Galois action is a group action: acting by στ is acting by σ after τ. -/
theorem tateLevelTwoGaloisAction_mul
    (σ τ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) :
    tateLevelTwoGaloisAction (σ * τ) =
      (tateLevelTwoGaloisAction τ).trans (tateLevelTwoGaloisAction σ) := by
  ext P
  exact congrArg Subtype.val
    (LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_mul_apply
      curveY2EqX3SubX 2 σ τ P)

/-- The Galois action on E[2] is ZMod 2-linear. -/
theorem tateLevelTwoGaloisAction_zmod_smul
    (σ : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase)
    (c : ZMod 2) (P : tateLevelTwoTorsion) :
    tateLevelTwoGaloisAction σ (c • P) =
      c • (tateLevelTwoGaloisAction σ P) :=
  LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_zmod_smul
    curveY2EqX3SubX 2 σ c P

/-! ## The absolute Galois group of Q as a profinite group -/

/-- The absolute Galois group of Q as a profinite group. -/
noncomputable abbrev rationalAbsoluteGaloisGroup : ProfiniteGrp :=
  Iut.AbsoluteGaloisProfinite ℚ

/-- Its underlying type is the group of Q-algebra automorphisms of the separable
closure, which is the group acting on the level-two Tate module. -/
theorem rationalAbsoluteGaloisGroup_coe :
    (rationalAbsoluteGaloisGroup : Type) =
      (tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) :=
  rfl

/-! ## Total group, anabelioid, and the elliptic-curve D-prime-strip -/

/-- The finite-level total fundamental group: absolute Galois group of Q times the
level-two Tate module. -/
noncomputable abbrev tateLevelTwoAnabelioidTotalGroup : ProfiniteGrp :=
  profiniteProduct rationalAbsoluteGaloisGroup tateLevelTwoProfiniteGroup

/-- The projection of the total group onto the absolute Galois group. -/
noncomputable abbrev tateLevelTwoAnabelioidProjection :
    tateLevelTwoAnabelioidTotalGroup ⟶ rationalAbsoluteGaloisGroup :=
  profiniteProductFst _ _

theorem tateLevelTwoAnabelioidProjection_surjective :
    Function.Surjective (tateLevelTwoAnabelioidProjection).hom.toMonoidHom :=
  profiniteProductFst_surjective _ _

/-- The kernel of the genuine projection is the concrete level-two Tate module. -/
noncomputable def tateLevelTwoAnabelioidProjection_kerMulEquiv :
    (tateLevelTwoAnabelioidProjection).hom.toMonoidHom.ker ≃*
      (tateLevelTwoProfiniteGroup : Type) :=
  prodFstKerMulEquiv rationalAbsoluteGaloisGroup (tateLevelTwoProfiniteGroup : Type)

/-- The anabelioid of the finite-level Tate module E[2]. -/
noncomputable abbrev tateLevelTwoAnabelioid : Iut.EtaleFundamentalGroup :=
  Iut.continuousActionEtaleFundamentalGroup tateLevelTwoProfiniteGroup

/-- The anabelioid of the absolute Galois group of Q. -/
noncomputable abbrev rationalAbsoluteGaloisAnabelioid : Iut.EtaleFundamentalGroup :=
  Iut.continuousActionEtaleFundamentalGroup rationalAbsoluteGaloisGroup

/-- The anabelioid of the finite-level total group. -/
noncomputable abbrev tateLevelTwoAnabelioidTotal : Iut.EtaleFundamentalGroup :=
  Iut.continuousActionEtaleFundamentalGroup tateLevelTwoAnabelioidTotalGroup

theorem tateLevelTwoAnabelioid_group :
    tateLevelTwoAnabelioid.group = tateLevelTwoProfiniteGroup :=
  rfl

theorem rationalAbsoluteGaloisAnabelioid_group :
    rationalAbsoluteGaloisAnabelioid.group = rationalAbsoluteGaloisGroup :=
  rfl

theorem tateLevelTwoAnabelioidTotal_group :
    tateLevelTwoAnabelioidTotal.group = tateLevelTwoAnabelioidTotalGroup :=
  rfl

/-- The pointed anabelioid morphism induced by the projection. -/
noncomputable abbrev tateLevelTwoAnabelioidMorphism :
    Iut.SourcePointedAnabelioidHom tateLevelTwoAnabelioidTotal
      rationalAbsoluteGaloisAnabelioid :=
  Iut.continuousActionPointedHom tateLevelTwoAnabelioidProjection

/-- The map on certified fundamental groups is the genuine projection. -/
theorem tateLevelTwoAnabelioidMorphism_fundamentalGroup_apply
    (x : tateLevelTwoAnabelioidTotal.group) :
    (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
        tateLevelTwoAnabelioidMorphism).hom.toMonoidHom x =
      (tateLevelTwoAnabelioidProjection).hom.toMonoidHom x :=
  Iut.continuousActionPointedHom_fundamentalGroupHom tateLevelTwoAnabelioidProjection x

theorem tateLevelTwoAnabelioidMorphism_fundamentalGroup_surjective :
    Function.Surjective (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
      tateLevelTwoAnabelioidMorphism).hom.toMonoidHom := by
  intro y
  obtain ⟨x, hx⟩ := tateLevelTwoAnabelioidProjection_surjective y
  exact ⟨x, by rw [tateLevelTwoAnabelioidMorphism_fundamentalGroup_apply]; exact hx⟩

/-- The concrete elliptic-curve anabelioid D-prime-strip: a single place, whose
fundamental group is the certified fundamental group of
B(Gal(Qbar/Q) x E[2]) and whose Galois group is the certified fundamental group
of B(Gal(Qbar/Q)). -/
noncomputable def ellipticCurveAnabelioidDPrimeStrip : DPrimeStrip Unit where
  Pi _ := tateLevelTwoAnabelioidTotal.group
  groupPi _ := inferInstance
  G _ := rationalAbsoluteGaloisAnabelioid.group
  groupG _ := inferInstance
  proj _ := (tateLevelTwoAnabelioidProjection).hom.toMonoidHom
  proj_surjective _ := tateLevelTwoAnabelioidProjection_surjective

/-- The projection of the elliptic-curve D-prime-strip is the map on certified
fundamental groups induced by the pointed anabelioid morphism. -/
theorem ellipticCurveAnabelioidDPrimeStrip_proj_eq_anabelioidMorphism
    (x : ellipticCurveAnabelioidDPrimeStrip.Pi ()) :
    ellipticCurveAnabelioidDPrimeStrip.proj () x =
      (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
        tateLevelTwoAnabelioidMorphism).hom.toMonoidHom x :=
  (tateLevelTwoAnabelioidMorphism_fundamentalGroup_apply x).symm

/-- The geometric kernel of the elliptic-curve D-prime-strip is the kernel of the
genuine projection, i.e. the concrete level-two Tate module. -/
theorem ellipticCurveAnabelioidDPrimeStrip_geometric_eq_projectionKernel :
    ellipticCurveAnabelioidDPrimeStrip.geometric () =
      (tateLevelTwoAnabelioidProjection).hom.toMonoidHom.ker :=
  rfl

/-- The geometric kernel of the elliptic-curve D-prime-strip is multiplicatively
equivalent to the concrete level-two Tate module E[2]. -/
noncomputable def ellipticCurveAnabelioidDPrimeStrip_geometricMulEquiv :
    (ellipticCurveAnabelioidDPrimeStrip.geometric ()) ≃*
      (tateLevelTwoProfiniteGroup : Type) :=
  tateLevelTwoAnabelioidProjection_kerMulEquiv

/-- The geometric kernel contains a nontrivial element. -/
theorem ellipticCurveAnabelioidDPrimeStrip_geometric_nontrivialElement :
    ∃ x : ellipticCurveAnabelioidDPrimeStrip.Pi (),
      x ∈ ellipticCurveAnabelioidDPrimeStrip.geometric () ∧ x ≠ 1 := by
  obtain ⟨x, hx⟩ := tateLevelTwoProfiniteGroup_exists_ne_one
  let y : ellipticCurveAnabelioidDPrimeStrip.geometric () :=
    (ellipticCurveAnabelioidDPrimeStrip_geometricMulEquiv).symm x
  refine ⟨y.1, y.2, ?_⟩
  intro hy
  have h1 : ellipticCurveAnabelioidDPrimeStrip_geometricMulEquiv y = x :=
    (ellipticCurveAnabelioidDPrimeStrip_geometricMulEquiv).apply_symm_apply x
  have hy1 : y = 1 := Subtype.ext hy
  rw [hy1, map_one] at h1
  exact hx h1.symm

theorem ellipticCurveAnabelioidDPrimeStrip_geometric_ne_bot :
    ellipticCurveAnabelioidDPrimeStrip.geometric () ≠ ⊥ := by
  obtain ⟨x, hxmem, hxne⟩ :=
    ellipticCurveAnabelioidDPrimeStrip_geometric_nontrivialElement
  intro hbot
  exact hxne (Subgroup.mem_bot.mp (hbot ▸ hxmem))

theorem ellipticCurveAnabelioidDPrimeStrip_hasNontrivialGeometricKernel :
    HasNontrivialGeometricKernel ellipticCurveAnabelioidDPrimeStrip :=
  ⟨(), ellipticCurveAnabelioidDPrimeStrip_geometric_ne_bot⟩

/-! ## The concrete kernel is not the reduced Z/2 model -/

theorem tateLevelTwoPointOneZero_ne_minusOneZero :
    tateLevelTwoPointOneZero ≠ tateLevelTwoPointMinusOneZero := by
  intro h
  have hcoords := (WeierstrassCurve.Affine.Point.some.injEq 1 0 tateNonsingularOneZero
    (-1) 0 tateNonsingularMinusOneZero).mp (congrArg Subtype.val h)
  norm_num at hcoords

/-- Three distinct explicit elements of the level-two Tate module. -/
noncomputable def tateLevelTwoThreePoints : Fin 3 → tateLevelTwoTorsion
  | ⟨0, _⟩ => tateLevelTwoPointZeroZero
  | ⟨1, _⟩ => tateLevelTwoPointOneZero
  | ⟨2, _⟩ => tateLevelTwoPointMinusOneZero
  | ⟨_ + 3, hn⟩ => absurd hn (by omega)

theorem tateLevelTwoThreePoints_injective :
    Function.Injective tateLevelTwoThreePoints := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij tateLevelTwoPointZeroZero_ne_oneZero
  · exact absurd hij tateLevelTwoPointZeroZero_ne_minusOneZero
  · exact absurd hij.symm tateLevelTwoPointZeroZero_ne_oneZero
  · rfl
  · exact absurd hij tateLevelTwoPointOneZero_ne_minusOneZero
  · exact absurd hij.symm tateLevelTwoPointZeroZero_ne_minusOneZero
  · exact absurd hij.symm tateLevelTwoPointOneZero_ne_minusOneZero
  · rfl

theorem tateLevelTwoTorsion_card_ge_three :
    3 ≤ Nat.card tateLevelTwoTorsion := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective tateLevelTwoThreePoints
    tateLevelTwoThreePoints_injective

/-- The level-two Tate module is not cyclic of order two. -/
theorem tateLevelTwoTorsion_not_mulEquiv_zmod_two :
    ¬ Nonempty (Multiplicative tateLevelTwoTorsion ≃* Multiplicative (ZMod 2)) := by
  rintro ⟨e⟩
  have hcard : Nat.card (Multiplicative tateLevelTwoTorsion) =
      Nat.card (Multiplicative (ZMod 2)) :=
    Nat.card_congr e.toEquiv
  have hmod : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card,
      show Fintype.card (Multiplicative (ZMod 2)) = Fintype.card (ZMod 2) from rfl,
      ZMod.card]
  rw [hmod] at hcard
  have hge : 3 ≤ Nat.card (Multiplicative tateLevelTwoTorsion) :=
    tateLevelTwoTorsion_card_ge_three
  omega

/-- The geometric kernel of the elliptic-curve D-prime-strip is not the reduced
Z/2 kernel model of the previous file. -/
theorem ellipticCurveAnabelioidDPrimeStrip_geometric_not_zmodTwo :
    ¬ Nonempty ((ellipticCurveAnabelioidDPrimeStrip.geometric ()) ≃*
      (reducedGeometricKernelModel : Type)) := by
  rintro ⟨e⟩
  apply tateLevelTwoTorsion_not_mulEquiv_zmod_two
  exact ⟨(ellipticCurveAnabelioidDPrimeStrip_geometricMulEquiv).symm.trans e⟩


/-! ## The concrete torsion point (0,0) in the geometric kernel -/

/-- The nontrivial element of the geometric kernel corresponding to the concrete
2-torsion point (0,0) of y^2 = x^3 - x. -/
noncomputable def ellipticCurveAnabelioidDPrimeStrip_geometricPointZeroZero :
    ellipticCurveAnabelioidDPrimeStrip.geometric () :=
  (ellipticCurveAnabelioidDPrimeStrip_geometricMulEquiv).symm
    (Multiplicative.ofAdd tateLevelTwoPointZeroZero)

/-- Under the kernel equivalence, that element is the concrete 2-torsion point (0,0). -/
theorem ellipticCurveAnabelioidDPrimeStrip_geometricPointZeroZero_corresponds :
    ellipticCurveAnabelioidDPrimeStrip_geometricMulEquiv
        ellipticCurveAnabelioidDPrimeStrip_geometricPointZeroZero =
      Multiplicative.ofAdd tateLevelTwoPointZeroZero :=
  (ellipticCurveAnabelioidDPrimeStrip_geometricMulEquiv).apply_symm_apply _

/-- The concrete torsion point in the geometric kernel is nontrivial. -/
theorem ellipticCurveAnabelioidDPrimeStrip_geometricPointZeroZero_ne_one :
    (ellipticCurveAnabelioidDPrimeStrip_geometricPointZeroZero :
        ellipticCurveAnabelioidDPrimeStrip.Pi ()) ≠ 1 := by
  intro h
  have h1 := ellipticCurveAnabelioidDPrimeStrip_geometricPointZeroZero_corresponds
  have hy : ellipticCurveAnabelioidDPrimeStrip_geometricPointZeroZero = 1 := Subtype.ext h
  rw [hy, map_one] at h1
  have h2 : tateLevelTwoPointZeroZero = 0 := congrArg Multiplicative.toAdd h1.symm
  exact tateLevelTwoPointZeroZero_ne_zero h2

end LeanFormal.IUT.IUTII.Frobenioid.Example36
