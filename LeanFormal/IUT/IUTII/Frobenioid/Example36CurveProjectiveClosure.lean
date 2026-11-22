import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveConnectedness
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

/-!
# Foundation F3e: the projective closure of y^2 = x^3 - x, chart data and gluing card

This module continues Example36CurveScheme and Example36CurveConnectedness.  It
constructs the actual homogeneous equation of the projective closure of the affine
curve y^2 = x^3 - x, both affine charts (the chart Z = 1 is the task-83 affine curve
curveScheme K, the affine Weierstrass chart that models the ONCE-punctured curve
E \\ {O} with O = (0:1:0) at infinity; the chart Y != 0 is a second affine chart
carrying the point at infinity), the actual overlap localization schemes, and the
actual point at infinity.  The finite point P = (0,0) is a finite 2-torsion point of
the elliptic curve, not the Weierstrass group zero; it is present in the once-punctured
chart and is removed only in the two-punctured EXTRA subscheme E \\ {O,P}.

The two charts are glued along their overlap via Mathlib's Scheme.GlueData; the
glued scheme is the actual model of the projective closure used here, with its two
chart open immersions, its structure morphism over Spec K, its point at infinity
and its comparison with the task-83 affine curve.  No fake scheme and no fake
glued object is introduced.

## Actual content

* curveHomogeneousEquation: Y^2 * Z - X^3 + X * Z^2 in K[X,Y,Z];
* the two chart equations, proved by substitution: Z = 1 gives y^2 - x^3 + x (the
  task-83 affine curve) and Y = 1 gives t - s^3 + s * t^2;
* curveChartYScheme: the affine chart Y != 0, with its coordinate ring;
* curveInfinityPoint: the point at infinity (s,t) = (0,0) on the chart Y != 0,
  constructed as a maximal ideal via the evaluation at the origin (all values are
  substituted into the homogeneous relation);
* actual overlap schemes as Spec of the localizations at z-coordinate y and at
  t, with their structure morphisms to the two charts;
* the task-83 affine curve E \\ {O} and its two-punctured EXTRA open subscheme
  E \\ {O,P} are definitionally the chart Z = 1 and its puncture at the finite point P;
* the overlap transition ring equivalence `curveChartOverlapTransitionRingEquiv`
  and the scheme isomorphism `curveChartOverlapTransitionIso`, with both inverse
  laws proved from the localisation universal properties;
* the two-chart glue data `curveProjectiveSchemeGlueData`, the glued scheme
  `curveProjectiveGluedScheme`, the chart open immersions, the joint covering
  theorem, the point at infinity on the glued scheme and the structure morphism
  `curveProjectiveGluedStructureMap` over Spec K, which restricts to the two chart
  structure morphisms and is unique with this property;
* the actual inhabitants `curveProjectiveClosureGlueCard` and
  `curveProjectiveClosureCard` of the frozen cards, at universe 0 (the universe of
  the actual localisation construction in this file).

## Scope and remaining comparison

The model of the projective closure is the explicit gluing of the two affine
Weierstrass charts; it is constructed, not postulated.  The identification of this
glued model with a Mathlib `Proj` of the homogeneous coordinate ring (or with a
closed subscheme of a projective plane) is not formalized: this Mathlib checkout
has no `Proj` scheme API.  Properness of the structure morphism over Spec K is
also not proved here.  These are recorded as precise gaps, not as card fields.

No curve pi1, theta, q-pilot or Tate claim is made.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {K : Type u} [Field K]

/-! ## 1. The homogeneous equation and its affine charts -/

/-- The homogeneous equation Y^2 * Z - X^3 + X * Z^2 of the projective closure of
y^2 = x^3 - x, with coordinates X = X 0, Y = X 1, Z = X 2. -/
def curveHomogeneousEquation (K : Type u) [Field K] : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3 +
    MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2

/-- Substitution X = x, Y = y, Z = 1 (the chart Z != 0). -/
def curveChartZSubstitution (K : Type u) [Field K] : Fin 3 → MvPolynomial (Fin 2) K
  | ⟨0, _⟩ => MvPolynomial.X 0
  | ⟨1, _⟩ => MvPolynomial.X 1
  | ⟨2, _⟩ => 1
  | ⟨n + 3, h⟩ => absurd h (by omega)

/-- Substitution X = s, Y = 1, Z = t (the chart Y != 0). -/
def curveChartYSubstitution (K : Type u) [Field K] : Fin 3 → MvPolynomial (Fin 2) K
  | ⟨0, _⟩ => MvPolynomial.X 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => MvPolynomial.X 1
  | ⟨n + 3, h⟩ => absurd h (by omega)

/-- The chart Z != 0 of the homogeneous equation is the task-83 affine equation
y^2 - x^3 + x. -/
theorem curveHomogeneous_chartZ :
    MvPolynomial.aeval (curveChartZSubstitution K) (curveHomogeneousEquation K) =
      curveEquationPolynomial K := by
  simp [curveHomogeneousEquation, curveEquationPolynomial, curveChartZSubstitution]

/-- The chart Y != 0 equation t - s^3 + s * t^2. -/
def curveChartYPolynomial (K : Type u) [Field K] : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2

/-- The chart Y != 0 of the homogeneous equation is t - s^3 + s * t^2. -/
theorem curveHomogeneous_chartY :
    MvPolynomial.aeval (curveChartYSubstitution K) (curveHomogeneousEquation K) =
      curveChartYPolynomial K := by
  simp [curveHomogeneousEquation, curveChartYPolynomial, curveChartYSubstitution]

/-! ## 2. The second affine chart and the point at infinity -/

abbrev curveChartYIdeal (K : Type u) [Field K] : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {curveChartYPolynomial K}

abbrev curveChartYRing (K : Type u) [Field K] : Type u :=
  MvPolynomial (Fin 2) K ⧸ curveChartYIdeal K

abbrev curveChartYScheme (K : Type u) [Field K] : Scheme :=
  Spec (CommRingCat.of (curveChartYRing K))

/-- The structure morphism of the second affine chart over Spec K. -/
def curveChartYStructureMap (K : Type u) [Field K] :
    curveChartYScheme K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (curveChartYRing K)))

/-- Evaluation at (s,t) = (0,0) on the polynomial ring. -/
abbrev curveInfinityPolynomialEval (K : Type u) [Field K] :
    MvPolynomial (Fin 2) K →+* K :=
  MvPolynomial.eval (fun _ : Fin 2 => (0 : K))

/-- Evaluation at the origin factors through the chart Y != 0 coordinate ring. -/
abbrev curveInfinityEval (K : Type u) [Field K] : curveChartYRing K →+* K :=
  Ideal.Quotient.lift (curveChartYIdeal K) (curveInfinityPolynomialEval K) (by
    intro a ha
    have hle : curveChartYIdeal K ≤ RingHom.ker (curveInfinityPolynomialEval K) := by
      rw [curveChartYIdeal, Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change curveInfinityPolynomialEval K (curveChartYPolynomial K) = 0
      simp [curveInfinityPolynomialEval, curveChartYPolynomial]
    exact hle ha)

theorem curveInfinityEval_surjective (K : Type u) [Field K] :
    Function.Surjective (curveInfinityEval K) := by
  intro y
  refine ⟨Ideal.Quotient.mk (curveChartYIdeal K) (MvPolynomial.C y), ?_⟩
  rw [curveInfinityEval, Ideal.Quotient.lift_mk]
  simp [curveInfinityPolynomialEval]

abbrev curveInfinityIdeal (K : Type u) [Field K] : Ideal (curveChartYRing K) :=
  RingHom.ker (curveInfinityEval K)

noncomputable instance curveInfinityIdeal_isMaximal (K : Type u) [Field K] :
    (curveInfinityIdeal K).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (curveInfinityEval K) (curveInfinityEval_surjective K)

/-- The point at infinity on the chart Y != 0: its homogeneous coordinates are
[X:Y:Z] = [0:1:0] and its affine chart coordinates are (s,t) = (0,0). -/
abbrev curveInfinityPoint (K : Type u) [Field K] : curveChartYScheme K :=
  ⟨curveInfinityIdeal K, (curveInfinityIdeal_isMaximal K).isPrime⟩

/-! ## 3. Overlap localization schemes -/

/-- The overlap Z != 0, Y != 0 viewed on the task-83 chart: localization at y. -/
abbrev curveChartZOverlapRing (K : Type u) [Field K] : Type u :=
  Localization.Away (curveY K)

abbrev curveChartZOverlap (K : Type u) [Field K] : Scheme :=
  Spec (CommRingCat.of (curveChartZOverlapRing K))

/-- The actual structure morphism from the overlap to the task-83 affine curve. -/
def curveChartZOverlapMap (K : Type u) [Field K] :
    curveChartZOverlap K ⟶ curveScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (curveCoordinateRing K)
    (curveChartZOverlapRing K)))

/-- The overlap Z != 0, Y != 0 viewed on the second chart: localization at t. -/
abbrev curveChartYOverlapRing (K : Type u) [Field K] : Type u :=
  Localization.Away (Ideal.Quotient.mk (curveChartYIdeal K) (MvPolynomial.X 1))

abbrev curveChartYOverlap (K : Type u) [Field K] : Scheme :=
  Spec (CommRingCat.of (curveChartYOverlapRing K))

def curveChartYOverlapMap (K : Type u) [Field K] :
    curveChartYOverlap K ⟶ curveChartYScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (curveChartYRing K)
    (curveChartYOverlapRing K)))

/-! ## 4. The frozen gluing/comparison card -/

/-- The gluing data of the two affine charts of the projective closure: the
transition isomorphism of the overlaps, the Scheme.GlueData, the glued projective
scheme, its open immersions, the structure morphism over Spec K, and the point at
infinity on the glued scheme.  This structure is realized by
`curveProjectiveClosureGlueCard` at universe 0. -/
structure CurveProjectiveClosureGlueCard (K : Type u) [Field K] where
  /-- The transition isomorphism between the two overlap schemes. -/
  transitionIso : curveChartZOverlap K ≅ curveChartYOverlap K
  /-- The actual glue data of the two charts. -/
  glueData : Scheme.GlueData
  /-- The glued projective curve. -/
  projectiveScheme : Scheme
  /-- The glued projective curve is the glued scheme of the glue data. -/
  projectiveScheme_eq_glued : projectiveScheme = glueData.glued
  /-- The open immersion of the first chart (Z != 0). -/
  chartZOpenImmersion : curveScheme K ⟶ projectiveScheme
  [chartZOpenImmersion_isOpenImmersion : IsOpenImmersion chartZOpenImmersion]
  /-- The open immersion of the second chart (Y != 0). -/
  chartYOpenImmersion : curveChartYScheme K ⟶ projectiveScheme
  [chartYOpenImmersion_isOpenImmersion : IsOpenImmersion chartYOpenImmersion]
  /-- The structure morphism of the projective closure over Spec K. -/
  structureMap : projectiveScheme ⟶ Spec (CommRingCat.of K)
  /-- The point at infinity on the glued projective scheme. -/
  pointAtInfinity : projectiveScheme

def CurveProjectiveClosureGlueCardRealized (K : Type u) [Field K] : Prop :=
  Nonempty (CurveProjectiveClosureGlueCard K)

/-- The task-83 affine curve is exactly the first chart Z = 1 of the homogeneous
equation, i.e. the ONCE-punctured affine model E \\ {O}: its coordinate ring is the
chart-Z coordinate ring and its scheme is definitionally the first affine chart. -/
theorem curveScheme_is_chartZ (K : Type u) [Field K] :
    curveScheme K = Spec (CommRingCat.of (MvPolynomial (Fin 2) K ⧸
      Ideal.span {curveEquationPolynomial K})) := rfl

/-- The two-punctured EXTRA open subscheme is exactly the chart-Z puncture at the
finite point P = (0,0); it is E \\ {O,P}, not the once-punctured source. -/
theorem curveTwoPuncturedScheme_is_chartZ_puncture (K : Type u) [Field K] :
    curveTwoPuncturedScheme K = (curveTwoPuncturedOpens K : Scheme) := rfl

/-- The affine chart Z = 1 of the projective closure is the ONCE-punctured curve
E \\ {O}: the point at infinity O = (0:1:0) is not in the affine chart and the
finite point P = (0,0) is present. -/
theorem curveScheme_is_affineChart_oncePunctured (K : Type u) [Field K] :
    curveScheme K = Spec (CommRingCat.of (MvPolynomial (Fin 2) K ⧸
        Ideal.span {curveEquationPolynomial K})) := rfl

/-- The finite point P = (0,0) removed by the two-punctured extra subscheme is a
finite 2-torsion point of the elliptic curve y^2 = x^3 - x, not the Weierstrass
group zero O. -/
theorem rationalTwoTorsionPoint_is_finiteTwoTorsion :
    (2 : ℕ) • rationalTwoTorsionPoint = 0 ∧ rationalTwoTorsionPoint ≠ 0 :=
  ⟨rationalTwoTorsionPoint_two_nsmul, rationalTwoTorsionPoint_ne_zero⟩


/-! ## 5. Actual chart facts and the comparison to CurveProjectiveClosureCard -/

/-- The actual chart computations: the homogeneous equation specializes to the two
affine chart equations, and the evaluation at the origin of the second chart is
surjective (giving the actual point at infinity). -/
theorem curveProjectiveClosureCharts_actual (K : Type u) [Field K] :
    MvPolynomial.aeval (curveChartZSubstitution K) (curveHomogeneousEquation K) =
        curveEquationPolynomial K ∧
      MvPolynomial.aeval (curveChartYSubstitution K) (curveHomogeneousEquation K) =
        curveChartYPolynomial K ∧
      Function.Surjective (curveInfinityEval K) :=
  ⟨curveHomogeneous_chartZ, curveHomogeneous_chartY, curveInfinityEval_surjective K⟩

/-- The actual affine-open field of CurveProjectiveClosureCard: its affine open is
the once-punctured curve curveScheme K = E \\ {O} (definitionally, the chart Z = 1),
and the extra two-punctured open subscheme is curveTwoPuncturedScheme K = E \\ {O,P}. -/
theorem curveProjectiveClosureCard_affineField_actual (K : Type u) [Field K] :
    curveScheme K = Spec (CommRingCat.of (MvPolynomial (Fin 2) K ⧸
        Ideal.span {curveEquationPolynomial K})) ∧
      curveTwoPuncturedScheme K = (curveTwoPuncturedOpens K : Scheme) :=
  ⟨rfl, rfl⟩

/-- The comparison package of the projective closure: the glued projective scheme,
its structure morphism and its point at infinity.  It is realized below at universe
0 by `curveProjectiveClosureGlueCard`. -/
def curveProjectiveClosureRemainingComparison (K : Type u) [Field K] : Prop :=
  CurveProjectiveClosureGlueCardRealized K

/-- The CurveProjectiveClosureCard fields: the projective scheme, its structure map,
the affine-open comparison and the point at infinity on the glued scheme.  It is
realized below at universe 0 by `curveProjectiveClosureCard`. -/
def curveProjectiveClosureCardRemainingFields (K : Type u) [Field K] : Prop :=
  CurveProjectiveClosureCardRealized K

/-! ## 7. Actual transition maps between the two overlap localisations

These are the actual transition maps: the forward ring hom `phi : A0 →+* A1` and
the inverse-direction ring hom `psi : A1 →+* A0` between the two overlap
localisation rings, at universe 0 (K : Type).  They are built from the
localisation-away universal property; the two composition identities
`psi_phi`/`phi_psi`, the induced scheme isomorphism
`curveChartOverlapTransitionIso` and the two-chart Scheme.GlueData
`curveProjectiveSchemeGlueData` are proved later in this file. -/


variable (K : Type) [Field K]

abbrev R0 (K : Type) [Field K] : Type := curveCoordinateRing K
abbrev R1 (K : Type) [Field K] : Type := curveChartYRing K
abbrev A0 (K : Type) [Field K] : Type := curveChartZOverlapRing K
abbrev A1 (K : Type) [Field K] : Type := curveChartYOverlapRing K

abbrev tbar (K : Type) [Field K] : R1 K :=
  Ideal.Quotient.mk (curveChartYIdeal K) (MvPolynomial.X 1)

abbrev sbar (K : Type) [Field K] : R1 K :=
  Ideal.Quotient.mk (curveChartYIdeal K) (MvPolynomial.X 0)

abbrev tOne (K : Type) [Field K] : Submonoid.powers (tbar K) :=
  ⟨1, ⟨0, by simp⟩⟩

abbrev tPow (K : Type) [Field K] : Submonoid.powers (tbar K) :=
  ⟨tbar K, ⟨1, by simp [pow_one]⟩⟩

noncomputable abbrev t1 (K : Type) [Field K] : A1 K :=
  Localization.mk (tbar K) (tOne K)

noncomputable abbrev s1 (K : Type) [Field K] : A1 K :=
  Localization.mk (sbar K) (tOne K)

noncomputable abbrev tInv (K : Type) [Field K] : A1 K :=
  Localization.mk (1 : R1 K) (tPow K)

theorem t1_mul_tInv (K : Type) [Field K] : t1 K * tInv K = 1 := by
  rw [t1, tInv, Localization.mk_mul]
  rw [show tOne K * tPow K = tPow K from Subtype.ext (by simp [tOne, tPow])]
  simpa using Localization.mk_self (tPow K)

theorem tInv_mul_t1 (K : Type) [Field K] : tInv K * t1 K = 1 := by
  rw [mul_comm, t1_mul_tInv]

theorem chartYRelation_quotient (K : Type) [Field K] :
    Ideal.Quotient.mk (curveChartYIdeal K) (curveChartYPolynomial K) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_dvd]

theorem chartYPolynomial_eq (K : Type) [Field K] :
    Ideal.Quotient.mk (curveChartYIdeal K) (curveChartYPolynomial K) =
      tbar K - sbar K ^ 3 + sbar K * tbar K ^ 2 := by
  simp [curveChartYPolynomial, tbar, sbar]

theorem hrel (K : Type) [Field K] :
    t1 K = s1 K ^ 3 - s1 K * t1 K ^ 2 := by
  have hR : tbar K - sbar K ^ 3 + sbar K * tbar K ^ 2 = 0 := by
    rw [← chartYPolynomial_eq K]
    exact chartYRelation_quotient K
  have h := congrArg (algebraMap (R1 K) (A1 K)) hR
  simp only [map_sub, map_add, map_pow, map_mul, map_zero] at h
  have h1 : algebraMap (R1 K) (A1 K) (tbar K) = t1 K := rfl
  have h2 : algebraMap (R1 K) (A1 K) (sbar K) = s1 K := rfl
  rw [h1, h2] at h
  linear_combination h

theorem hzero (K : Type) [Field K] :
    tInv K ^ 2 - (s1 K * tInv K) ^ 3 + s1 K * tInv K = 0 := by
  have e1 : tInv K ^ 3 * t1 K = tInv K ^ 2 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, mul_assoc,
      tInv_mul_t1 K, mul_one]
  have e2 : tInv K ^ 3 * t1 K ^ 2 = tInv K := by
    calc tInv K ^ 3 * t1 K ^ 2 = tInv K * (tInv K * t1 K) ^ 2 := by ring
      _ = tInv K * 1 ^ 2 := by rw [tInv_mul_t1 K]
      _ = tInv K := by ring
  calc tInv K ^ 2 - (s1 K * tInv K) ^ 3 + s1 K * tInv K
      = tInv K ^ 3 * (t1 K - s1 K ^ 3 + s1 K * t1 K ^ 2) := by
        rw [show tInv K ^ 3 * (t1 K - s1 K ^ 3 + s1 K * t1 K ^ 2)
            = tInv K ^ 3 * t1 K - s1 K ^ 3 * tInv K ^ 3 +
              s1 K * tInv K ^ 3 * t1 K ^ 2 from by ring]
        rw [e1, mul_assoc (s1 K) (tInv K ^ 3) (t1 K ^ 2), e2]
        ring
    _ = 0 := by
        have h' : t1 K - s1 K ^ 3 + s1 K * t1 K ^ 2 = 0 := by
          linear_combination hrel K
        rw [h']
        ring

abbrev evalVals (K : Type) [Field K] : Fin 2 → A1 K :=
  ![s1 K * tInv K, tInv K]

theorem alphaPoly_zero (K : Type) [Field K] :
    MvPolynomial.eval₂Hom (algebraMap K (A1 K)) (evalVals K)
      (curveEquationPolynomial K) = 0 := by
  simp [curveEquationPolynomial, evalVals, hzero K]

noncomputable def alphaPoly (K : Type) [Field K] :
    MvPolynomial (Fin 2) K →+* A1 K :=
  MvPolynomial.eval₂Hom (algebraMap K (A1 K)) (evalVals K)

theorem alphaPoly_mem_ker (K : Type) [Field K] :
    curveCoordinateIdeal K ≤ RingHom.ker (alphaPoly K) := by
  rw [curveCoordinateIdeal, Ideal.span_le]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst ha
  exact RingHom.mem_ker.mpr (alphaPoly_zero K)

noncomputable def alpha (K : Type) [Field K] : R0 K →+* A1 K :=
  Ideal.Quotient.lift (curveCoordinateIdeal K) (alphaPoly K) (alphaPoly_mem_ker K)

theorem alpha_curveY (K : Type) [Field K] :
    alpha K (curveY K) = tInv K := by
  simp [alpha, curveY, alphaPoly, evalVals]

theorem alpha_curveY_isUnit (K : Type) [Field K] :
    IsUnit (alpha K (curveY K)) := by
  rw [alpha_curveY]
  exact isUnit_iff_exists_inv.mpr ⟨t1 K, tInv_mul_t1 K⟩

noncomputable def phi (K : Type) [Field K] : A0 K →+* A1 K :=
  Localization.awayLift (alpha K) (curveY K) (alpha_curveY_isUnit K)


/-! ## Symmetric inverse map psi : A1 → A0 -/

abbrev yOne (K : Type) [Field K] : Submonoid.powers (curveY K) :=
  ⟨1, ⟨0, by simp⟩⟩

abbrev yPow (K : Type) [Field K] : Submonoid.powers (curveY K) :=
  ⟨curveY K, ⟨1, by simp [pow_one]⟩⟩

noncomputable abbrev y0 (K : Type) [Field K] : A0 K :=
  Localization.mk (curveY K) (yOne K)

noncomputable abbrev x0 (K : Type) [Field K] : A0 K :=
  Localization.mk (curveX K) (yOne K)

noncomputable abbrev yInv (K : Type) [Field K] : A0 K :=
  Localization.mk (1 : R0 K) (yPow K)

theorem y0_mul_yInv (K : Type) [Field K] : y0 K * yInv K = 1 := by
  rw [y0, yInv, Localization.mk_mul]
  rw [show yOne K * yPow K = yPow K from Subtype.ext (by simp [yOne, yPow])]
  simpa using Localization.mk_self (yPow K)

theorem yInv_mul_y0 (K : Type) [Field K] : yInv K * y0 K = 1 := by
  rw [mul_comm, y0_mul_yInv]

theorem hrelW (K : Type) [Field K] : y0 K ^ 2 = x0 K ^ 3 - x0 K := by
  have h := congrArg (algebraMap (R0 K) (A0 K)) (curveWeierstrassRelation K)
  simp only [map_pow, map_sub] at h
  have h1 : algebraMap (R0 K) (A0 K) (curveY K) = y0 K := rfl
  have h2 : algebraMap (R0 K) (A0 K) (curveX K) = x0 K := rfl
  rw [h1, h2] at h
  exact h

theorem hzero2 (K : Type) [Field K] :
    yInv K - (x0 K * yInv K) ^ 3 + x0 K * yInv K * yInv K ^ 2 = 0 := by
  rw [show yInv K - (x0 K * yInv K) ^ 3 + x0 K * yInv K * yInv K ^ 2 =
    yInv K - (x0 K ^ 3 - x0 K) * yInv K ^ 3 from by ring]
  rw [← hrelW K]
  have hy : y0 K ^ 2 * yInv K ^ 3 = yInv K := by
    calc y0 K ^ 2 * yInv K ^ 3 = yInv K * (y0 K * yInv K) ^ 2 := by ring
      _ = yInv K * 1 ^ 2 := by rw [y0_mul_yInv K]
      _ = yInv K := by ring
  rw [hy]
  ring

abbrev betaVals (K : Type) [Field K] : Fin 2 → A0 K :=
  ![x0 K * yInv K, yInv K]

noncomputable def betaPoly (K : Type) [Field K] :
    MvPolynomial (Fin 2) K →+* A0 K :=
  MvPolynomial.eval₂Hom (algebraMap K (A0 K)) (betaVals K)

theorem betaPoly_zero (K : Type) [Field K] :
    betaPoly K (curveChartYPolynomial K) = 0 := by
  simp [betaPoly, curveChartYPolynomial, betaVals, hzero2 K]

theorem betaPoly_mem_ker (K : Type) [Field K] :
    curveChartYIdeal K ≤ RingHom.ker (betaPoly K) := by
  rw [curveChartYIdeal, Ideal.span_le]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst ha
  exact RingHom.mem_ker.mpr (betaPoly_zero K)

noncomputable def beta (K : Type) [Field K] : R1 K →+* A0 K :=
  Ideal.Quotient.lift (curveChartYIdeal K) (betaPoly K) (betaPoly_mem_ker K)

theorem beta_tbar (K : Type) [Field K] : beta K (tbar K) = yInv K := by
  simp [beta, betaPoly, betaVals, tbar]

theorem beta_tbar_isUnit (K : Type) [Field K] : IsUnit (beta K (tbar K)) := by
  rw [beta_tbar]
  exact isUnit_iff_exists_inv.mpr ⟨y0 K, yInv_mul_y0 K⟩

noncomputable def psi (K : Type) [Field K] : A1 K →+* A0 K :=
  Localization.awayLift (beta K) (tbar K) (beta_tbar_isUnit K)

theorem psi_s1 (K : Type) [Field K] : psi K (s1 K) = x0 K * yInv K := by
  have hone : tOne K = 1 := Subtype.ext rfl
  rw [s1, hone, Localization.mk_one_eq_algebraMap]
  have h := IsLocalization.Away.lift_comp (R := R1 K) (S := A1 K) (x := tbar K) (g := beta K) (beta_tbar_isUnit K)
  have h' := RingHom.congr_fun h (sbar K)
  simpa [psi, beta, betaPoly, betaVals] using h'

theorem psi_t1 (K : Type) [Field K] : psi K (t1 K) = yInv K := by
  have hone : tOne K = 1 := Subtype.ext rfl
  rw [t1, hone, Localization.mk_one_eq_algebraMap]
  have h := IsLocalization.Away.lift_comp (R := R1 K) (S := A1 K) (x := tbar K) (g := beta K) (beta_tbar_isUnit K)
  have h' := RingHom.congr_fun h (tbar K)
  simpa [psi, beta, betaPoly, betaVals] using h'

theorem psi_tInv (K : Type) [Field K] : psi K (tInv K) = y0 K := by
  have hprod : psi K (tInv K) * yInv K = 1 := by
    calc psi K (tInv K) * yInv K = psi K (tInv K) * psi K (t1 K) := by rw [psi_t1 K]
      _ = psi K (tInv K * t1 K) := by rw [map_mul]
      _ = psi K 1 := by rw [tInv_mul_t1 K]
      _ = 1 := map_one (psi K)
  calc psi K (tInv K) = psi K (tInv K) * (yInv K * y0 K) := by rw [yInv_mul_y0 K]; ring
    _ = (psi K (tInv K) * yInv K) * y0 K := by ring
    _ = 1 * y0 K := by rw [hprod]
    _ = y0 K := by ring


open AlgebraicGeometry CategoryTheory

theorem x0_eq_algebraMap (K : Type) [Field K] :
    x0 K = algebraMap (R0 K) (A0 K) (curveX K) := by
  have hone : yOne K = 1 := Subtype.ext rfl
  rw [x0, hone]
  exact Localization.mk_one_eq_algebraMap (M := Submonoid.powers (curveY K)) (curveX K)

theorem y0_eq_algebraMap (K : Type) [Field K] :
    y0 K = algebraMap (R0 K) (A0 K) (curveY K) := by
  have hone : yOne K = 1 := Subtype.ext rfl
  rw [y0, hone]
  exact Localization.mk_one_eq_algebraMap (M := Submonoid.powers (curveY K)) (curveY K)

noncomputable def gammaPoly (K : Type) [Field K] :
    MvPolynomial (Fin 2) K →+* A0 K :=
  MvPolynomial.eval₂Hom (algebraMap K (A0 K)) ![x0 K, y0 K]

theorem gammaPoly_eq (K : Type) [Field K] :
    gammaPoly K = (algebraMap (R0 K) (A0 K)).comp
      (Ideal.Quotient.mk (curveCoordinateIdeal K)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change gammaPoly K (MvPolynomial.C a) =
      ((algebraMap (R0 K) (A0 K)).comp (Ideal.Quotient.mk (curveCoordinateIdeal K))) (MvPolynomial.C a)
    rw [RingHom.comp_apply]
    have hmk : Ideal.Quotient.mk (curveCoordinateIdeal K) (MvPolynomial.C a) =
        algebraMap K (R0 K) a := by
      exact Ideal.Quotient.mk_algebraMap K (I := curveCoordinateIdeal K) a
    rw [hmk]
    simp only [gammaPoly, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply K (R0 K) (A0 K) a
  · intro i
    fin_cases i
    · change gammaPoly K (MvPolynomial.X 0) =
        ((algebraMap (R0 K) (A0 K)).comp (Ideal.Quotient.mk (curveCoordinateIdeal K))) (MvPolynomial.X 0)
      rw [RingHom.comp_apply]
      have hx : algebraMap (R0 K) (A0 K) ((Ideal.Quotient.mk (curveCoordinateIdeal K)) (MvPolynomial.X 0)) = x0 K := by
        rw [← x0_eq_algebraMap K]
      rw [hx]
      simp [gammaPoly]
    · change gammaPoly K (MvPolynomial.X 1) =
        ((algebraMap (R0 K) (A0 K)).comp (Ideal.Quotient.mk (curveCoordinateIdeal K))) (MvPolynomial.X 1)
      rw [RingHom.comp_apply]
      have hy : algebraMap (R0 K) (A0 K) ((Ideal.Quotient.mk (curveCoordinateIdeal K)) (MvPolynomial.X 1)) = y0 K := by
        rw [← y0_eq_algebraMap K]
      rw [hy]
      simp [gammaPoly]

theorem gammaPoly_apply (K : Type) [Field K] (p : MvPolynomial (Fin 2) K) :
    gammaPoly K p = algebraMap (R0 K) (A0 K) (Ideal.Quotient.mk (curveCoordinateIdeal K) p) := by
  have h := RingHom.congr_fun (gammaPoly_eq K) p
  simpa [RingHom.comp_apply] using h

theorem psi_comp_alphaPoly (K : Type) [Field K] :
    (psi K).comp (alphaPoly K) = gammaPoly K := by
  have hcomp : (psi K).comp (algebraMap (R1 K) (A1 K)) = beta K := by
    simpa [psi] using IsLocalization.Away.lift_comp (R := R1 K) (S := A1 K)
      (x := tbar K) (g := beta K) (beta_tbar_isUnit K)
  apply MvPolynomial.ringHom_ext
  · intro a
    change psi K (alphaPoly K (MvPolynomial.C a)) = gammaPoly K (MvPolynomial.C a)
    have ha : alphaPoly K (MvPolynomial.C a) = algebraMap K (A1 K) a := by
      simp [alphaPoly, MvPolynomial.eval₂Hom_C]
    rw [ha]
    have h1 : psi K (algebraMap K (A1 K) a) = algebraMap K (A0 K) a := by
      rw [IsScalarTower.algebraMap_apply K (R1 K) (A1 K)]
      rw [show psi K ((algebraMap (R1 K) (A1 K)) ((algebraMap K (R1 K)) a)) =
          beta K ((algebraMap K (R1 K)) a) from
        RingHom.congr_fun hcomp ((algebraMap K (R1 K)) a)]
      have hmk : Ideal.Quotient.mk (curveChartYIdeal K) (MvPolynomial.C a) =
          algebraMap K (R1 K) a := by
        exact Ideal.Quotient.mk_algebraMap K (I := curveChartYIdeal K) a
      rw [← hmk]
      simp [beta, betaPoly, MvPolynomial.eval₂Hom_C]
    rw [h1]
    simp [gammaPoly, MvPolynomial.eval₂Hom_C]
  · intro i
    fin_cases i
    · change psi K (alphaPoly K (MvPolynomial.X 0)) = gammaPoly K (MvPolynomial.X 0)
      have ha : alphaPoly K (MvPolynomial.X 0) = s1 K * tInv K := by
        simp [alphaPoly, evalVals, MvPolynomial.eval₂Hom_X']
      rw [ha, map_mul, psi_s1 K, psi_tInv K]
      rw [mul_assoc (x0 K) (yInv K) (y0 K), yInv_mul_y0 K, mul_one]
      have hg : gammaPoly K (MvPolynomial.X 0) = x0 K := by
        simp [gammaPoly]
      rw [hg]
    · change psi K (alphaPoly K (MvPolynomial.X 1)) = gammaPoly K (MvPolynomial.X 1)
      have ha : alphaPoly K (MvPolynomial.X 1) = tInv K := by
        simp [alphaPoly, evalVals, MvPolynomial.eval₂Hom_X']
      rw [ha, psi_tInv K]
      have hg : gammaPoly K (MvPolynomial.X 1) = y0 K := by
        simp [gammaPoly]
      rw [hg]

theorem psi_comp_alpha (K : Type) [Field K] :
    (psi K).comp (alpha K) = algebraMap (R0 K) (A0 K) := by
  apply Ideal.Quotient.ringHom_ext
  rw [RingHom.comp_assoc]
  change (psi K).comp (alphaPoly K) =
    (algebraMap (R0 K) (A0 K)).comp (Ideal.Quotient.mk (curveCoordinateIdeal K))
  rw [psi_comp_alphaPoly K, gammaPoly_eq K]

theorem psi_phi (K : Type) [Field K] : (psi K).comp (phi K) = RingHom.id (A0 K) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (curveY K))
  rw [RingHom.comp_assoc]
  rw [show (phi K).comp (algebraMap (R0 K) (A0 K)) = alpha K from
    IsLocalization.Away.lift_comp (R := R0 K) (S := A0 K) (x := curveY K)
      (g := alpha K) (alpha_curveY_isUnit K)]
  simpa using psi_comp_alpha K


theorem s1_eq_algebraMap (K : Type) [Field K] :
    s1 K = algebraMap (R1 K) (A1 K) (sbar K) := by
  have hone : tOne K = 1 := Subtype.ext rfl
  rw [s1, hone]
  exact Localization.mk_one_eq_algebraMap (M := Submonoid.powers (tbar K)) (sbar K)

theorem t1_eq_algebraMap (K : Type) [Field K] :
    t1 K = algebraMap (R1 K) (A1 K) (tbar K) := by
  have hone : tOne K = 1 := Subtype.ext rfl
  rw [t1, hone]
  exact Localization.mk_one_eq_algebraMap (M := Submonoid.powers (tbar K)) (tbar K)

noncomputable def deltaPoly (K : Type) [Field K] :
    MvPolynomial (Fin 2) K →+* A1 K :=
  MvPolynomial.eval₂Hom (algebraMap K (A1 K)) ![s1 K, t1 K]

theorem deltaPoly_eq (K : Type) [Field K] :
    deltaPoly K = (algebraMap (R1 K) (A1 K)).comp
      (Ideal.Quotient.mk (curveChartYIdeal K)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change deltaPoly K (MvPolynomial.C a) =
      ((algebraMap (R1 K) (A1 K)).comp (Ideal.Quotient.mk (curveChartYIdeal K))) (MvPolynomial.C a)
    rw [RingHom.comp_apply]
    have hmk : Ideal.Quotient.mk (curveChartYIdeal K) (MvPolynomial.C a) =
        algebraMap K (R1 K) a := by
      exact Ideal.Quotient.mk_algebraMap K (I := curveChartYIdeal K) a
    rw [hmk]
    simp only [deltaPoly, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply K (R1 K) (A1 K) a
  · intro i
    fin_cases i
    · change deltaPoly K (MvPolynomial.X 0) =
        ((algebraMap (R1 K) (A1 K)).comp (Ideal.Quotient.mk (curveChartYIdeal K))) (MvPolynomial.X 0)
      rw [RingHom.comp_apply]
      have hx : algebraMap (R1 K) (A1 K) ((Ideal.Quotient.mk (curveChartYIdeal K)) (MvPolynomial.X 0)) = s1 K :=
        (s1_eq_algebraMap K).symm
      rw [hx]
      simp only [deltaPoly, MvPolynomial.eval₂Hom_X']
      simp
    · change deltaPoly K (MvPolynomial.X 1) =
        ((algebraMap (R1 K) (A1 K)).comp (Ideal.Quotient.mk (curveChartYIdeal K))) (MvPolynomial.X 1)
      rw [RingHom.comp_apply]
      have hx : algebraMap (R1 K) (A1 K) ((Ideal.Quotient.mk (curveChartYIdeal K)) (MvPolynomial.X 1)) = t1 K :=
        (t1_eq_algebraMap K).symm
      rw [hx]
      simp only [deltaPoly, MvPolynomial.eval₂Hom_X']
      simp

theorem deltaPoly_apply (K : Type) [Field K] (p : MvPolynomial (Fin 2) K) :
    deltaPoly K p = algebraMap (R1 K) (A1 K) (Ideal.Quotient.mk (curveChartYIdeal K) p) := by
  have h := RingHom.congr_fun (deltaPoly_eq K) p
  simpa [RingHom.comp_apply] using h

theorem phi_comp_betaPoly (K : Type) [Field K] :
    (phi K).comp (betaPoly K) = deltaPoly K := by
  have hcompA0 : (phi K).comp (algebraMap (R0 K) (A0 K)) = alpha K := by
    simpa [phi] using IsLocalization.Away.lift_comp (R := R0 K) (S := A0 K)
      (x := curveY K) (g := alpha K) (alpha_curveY_isUnit K)
  have hy0 : phi K (y0 K) = tInv K := by
    rw [y0_eq_algebraMap K]
    rw [show (phi K) ((algebraMap (R0 K) (A0 K)) (curveY K)) = (alpha K) (curveY K) from
      RingHom.congr_fun hcompA0 (curveY K)]
    exact alpha_curveY K
  have hyInv : phi K (yInv K) = t1 K := by
    have hprod : phi K (yInv K) * tInv K = 1 := by
      calc phi K (yInv K) * tInv K = phi K (yInv K) * phi K (y0 K) := by rw [hy0]
        _ = phi K (yInv K * y0 K) := by rw [map_mul]
        _ = phi K 1 := by rw [yInv_mul_y0 K]
        _ = 1 := map_one (phi K)
    calc phi K (yInv K) = phi K (yInv K) * (tInv K * t1 K) := by rw [tInv_mul_t1 K]; ring
      _ = (phi K (yInv K) * tInv K) * t1 K := by ring
      _ = 1 * t1 K := by rw [hprod]
      _ = t1 K := by ring
  have hx0 : phi K (x0 K) = s1 K * tInv K := by
    rw [x0_eq_algebraMap K]
    rw [show (phi K) ((algebraMap (R0 K) (A0 K)) (curveX K)) = (alpha K) (curveX K) from
      RingHom.congr_fun hcompA0 (curveX K)]
    simp [alpha, alphaPoly, evalVals]
  apply MvPolynomial.ringHom_ext
  · intro a
    change phi K (betaPoly K (MvPolynomial.C a)) = deltaPoly K (MvPolynomial.C a)
    have hmk0 : Ideal.Quotient.mk (curveCoordinateIdeal K) (MvPolynomial.C a) =
        algebraMap K (R0 K) a := by
      exact Ideal.Quotient.mk_algebraMap K (I := curveCoordinateIdeal K) a
    have h1 : phi K (betaPoly K (MvPolynomial.C a)) =
        alpha K ((Ideal.Quotient.mk (curveCoordinateIdeal K)) (MvPolynomial.C a)) := by
      simp only [betaPoly, MvPolynomial.eval₂Hom_C]
      rw [IsScalarTower.algebraMap_apply K (R0 K) (A0 K)]
      rw [show (phi K) ((algebraMap (R0 K) (A0 K)) ((algebraMap K (R0 K)) a)) =
          (alpha K) ((algebraMap K (R0 K)) a) from
        RingHom.congr_fun hcompA0 ((algebraMap K (R0 K)) a)]
      rw [← hmk0]
    rw [h1]
    have hdelta : deltaPoly K (MvPolynomial.C a) = algebraMap K (A1 K) a := by
      simp only [deltaPoly, MvPolynomial.eval₂Hom_C]
    rw [hdelta]
    simp [alpha, alphaPoly, MvPolynomial.eval₂Hom_C]
  · intro i
    fin_cases i
    · change phi K (betaPoly K (MvPolynomial.X 0)) = deltaPoly K (MvPolynomial.X 0)
      have hL : betaPoly K (MvPolynomial.X 0) = x0 K * yInv K := by
        simp [betaPoly, betaVals]
      have hR : deltaPoly K (MvPolynomial.X 0) = s1 K := by
        simp [deltaPoly]
      rw [hL, hR, map_mul, hx0, hyInv]
      rw [mul_assoc (s1 K) (tInv K) (t1 K), tInv_mul_t1 K, mul_one]
    · change phi K (betaPoly K (MvPolynomial.X 1)) = deltaPoly K (MvPolynomial.X 1)
      have hL : betaPoly K (MvPolynomial.X 1) = yInv K := by
        simp [betaPoly, betaVals]
      have hR : deltaPoly K (MvPolynomial.X 1) = t1 K := by
        simp [deltaPoly]
      rw [hL, hR, hyInv]

theorem phi_comp_beta (K : Type) [Field K] :
    (phi K).comp (beta K) = algebraMap (R1 K) (A1 K) := by
  apply Ideal.Quotient.ringHom_ext
  rw [RingHom.comp_assoc]
  change (phi K).comp (betaPoly K) =
    (algebraMap (R1 K) (A1 K)).comp (Ideal.Quotient.mk (curveChartYIdeal K))
  rw [phi_comp_betaPoly K, deltaPoly_eq K]

theorem phi_psi (K : Type) [Field K] : (phi K).comp (psi K) = RingHom.id (A1 K) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tbar K))
  rw [RingHom.comp_assoc]
  rw [show (psi K).comp (algebraMap (R1 K) (A1 K)) = beta K from
    IsLocalization.Away.lift_comp (R := R1 K) (S := A1 K) (x := tbar K)
      (g := beta K) (beta_tbar_isUnit K)]
  simpa using phi_comp_beta K

/-! ## 1. The ring equivalence of the two overlap localisation rings -/

/-- The ring equivalence between the two overlap localisation rings: the forward
direction is `phi : A0 →+* A1` and the inverse direction is `psi : A1 →+* A0`. -/
noncomputable def curveChartOverlapTransitionRingEquiv (K : Type) [Field K] :
    A0 K ≃+* A1 K :=
  RingEquiv.ofRingHom (phi K) (psi K) (phi_psi K) (psi_phi K)

/-- The forward direction of the overlap transition ring equivalence is `phi`. -/
theorem curveChartOverlapTransitionRingEquiv_apply (K : Type) [Field K] (a : A0 K) :
    curveChartOverlapTransitionRingEquiv K a = phi K a := rfl

/-- The inverse direction of the overlap transition ring equivalence is `psi`. -/
theorem curveChartOverlapTransitionRingEquiv_symm_apply (K : Type) [Field K] (b : A1 K) :
    (curveChartOverlapTransitionRingEquiv K).symm b = psi K b := rfl

/-! ## 2. The transition isomorphism of the overlap schemes -/

/-- The isomorphism of overlap schemes induced by the ring equivalence, oriented from
the chart-Z overlap to the chart-Y overlap so that its forward morphism is
`Spec.map (CommRingCat.ofHom psi)`. -/
noncomputable def curveChartOverlapTransitionIso (K : Type) [Field K] :
    curveChartZOverlap K ≅ curveChartYOverlap K :=
  Iso.mk (Spec.map (CommRingCat.ofHom (psi K))) (Spec.map (CommRingCat.ofHom (phi K)))
    (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, psi_phi, CommRingCat.ofHom_id,
        Spec.map_id])
    (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, phi_psi, CommRingCat.ofHom_id,
        Spec.map_id])

/-- The forward morphism of the overlap transition isomorphism is `Spec.map psi`. -/
theorem curveChartOverlapTransitionIso_hom (K : Type) [Field K] :
    (curveChartOverlapTransitionIso K).hom = Spec.map (CommRingCat.ofHom (psi K)) :=
  rfl

/-- The inverse morphism of the overlap transition isomorphism is `Spec.map phi`. -/
theorem curveChartOverlapTransitionIso_inv (K : Type) [Field K] :
    (curveChartOverlapTransitionIso K).inv = Spec.map (CommRingCat.ofHom (phi K)) :=
  rfl

/-- The forward morphism of the transition isomorphism is `Spec` of the inverse of the
overlap transition ring equivalence. -/
theorem curveChartOverlapTransitionIso_hom_eq_ringEquiv (K : Type) [Field K] :
    (curveChartOverlapTransitionIso K).hom =
      Spec.map (CommRingCat.ofHom
        ((curveChartOverlapTransitionRingEquiv K).symm : A1 K →+* A0 K)) :=
  rfl

/-- The inverse morphism of the transition isomorphism is `Spec` of the forward
direction of the overlap transition ring equivalence. -/
theorem curveChartOverlapTransitionIso_inv_eq_ringEquiv (K : Type) [Field K] :
    (curveChartOverlapTransitionIso K).inv =
      Spec.map (CommRingCat.ofHom
        ((curveChartOverlapTransitionRingEquiv K) : A0 K →+* A1 K)) :=
  rfl

/-! ## 3. The overlap structure maps as `Spec` of the localisation maps -/

/-- The overlap-to-chart-Y map is `Spec` of the localisation map `R1 → A1`. -/
theorem curveChartYOverlapMap_eq (K : Type) [Field K] :
    curveChartYOverlapMap K = Spec.map (CommRingCat.ofHom (algebraMap (R1 K) (A1 K))) :=
  rfl

/-- The structure morphism of the chart-Y scheme is `Spec` of `K → R1`. -/
theorem curveChartYStructureMap_eq (K : Type) [Field K] :
    curveChartYStructureMap K = Spec.map (CommRingCat.ofHom (algebraMap K (R1 K))) :=
  rfl

/-- The overlap-to-chart-Z map is `Spec` of the localisation map `R0 → A0`. -/
theorem curveChartZOverlapMap_eq (K : Type) [Field K] :
    curveChartZOverlapMap K = Spec.map (CommRingCat.ofHom (algebraMap (R0 K) (A0 K))) :=
  rfl

/-- The structure morphism of the chart-Z affine curve is `Spec` of `K → R0`. -/
theorem curveSchemeStructureMap_eq (K : Type) [Field K] :
    curveSchemeStructureMap K = Spec.map (CommRingCat.ofHom (algebraMap K (R0 K))) :=
  rfl

/-! ## 4. Ring-level identities for the structure maps

The two structure morphisms over `Spec K` are `Spec` of the two `K`-algebra
structures on `A0 K`; here we record the ring-level identities from which their
agreement follows. -/

/-- `Spec` reverses a chain of three compositions. -/
theorem specMap_comp_three {R S T U : CommRingCat.{0}} (f : R ⟶ S) (g : S ⟶ T)
    (h : T ⟶ U) :
    Spec.map h ≫ Spec.map g ≫ Spec.map f = Spec.map (f ≫ g ≫ h) := by
  rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc]

/-- The localisation map `psi` is the `R1`-algebra structure of `beta`. -/
theorem psi_comp_algebraMap_R1 (K : Type) [Field K] :
    (psi K).comp (algebraMap (R1 K) (A1 K)) = beta K := by
  simp [psi]

/-- The localisation map `phi` is the `R0`-algebra structure of `alpha`. -/
theorem phi_comp_algebraMap_R0 (K : Type) [Field K] :
    (phi K).comp (algebraMap (R0 K) (A0 K)) = alpha K := by
  simp [phi]

/-- The two `K`-algebra structures on `A0 K` agree. -/
theorem algebraMap_comp_algebraMap_R0 (K : Type) [Field K] :
    (algebraMap (R0 K) (A0 K)).comp (algebraMap K (R0 K)) = algebraMap K (A0 K) := by
  ext a
  exact (IsScalarTower.algebraMap_apply K (R0 K) (A0 K) a).symm

/-- The two `K`-algebra structures on `A1 K` agree. -/
theorem algebraMap_comp_algebraMap_R1 (K : Type) [Field K] :
    (algebraMap (R1 K) (A1 K)).comp (algebraMap K (R1 K)) = algebraMap K (A1 K) := by
  ext a
  exact (IsScalarTower.algebraMap_apply K (R1 K) (A1 K) a).symm

/-- `alpha` acts on constants as the `K`-algebra structure of `A1 K`. -/
theorem alpha_comp_algebraMap_K (K : Type) [Field K] :
    (alpha K).comp (algebraMap K (R0 K)) = algebraMap K (A1 K) := by
  ext a
  rw [RingHom.comp_apply]
  have hmk : algebraMap K (R0 K) a =
      Ideal.Quotient.mk (curveCoordinateIdeal K) (MvPolynomial.C a) :=
    (Ideal.Quotient.mk_algebraMap K (I := curveCoordinateIdeal K) a).symm
  rw [hmk]
  simp [alpha, alphaPoly, MvPolynomial.eval₂Hom_C]

/-- `beta` acts on constants as the `K`-algebra structure of `A0 K`. -/
theorem beta_comp_algebraMap_K (K : Type) [Field K] :
    (beta K).comp (algebraMap K (R1 K)) = algebraMap K (A0 K) := by
  ext a
  rw [RingHom.comp_apply]
  have hmk : algebraMap K (R1 K) a =
      Ideal.Quotient.mk (curveChartYIdeal K) (MvPolynomial.C a) :=
    (Ideal.Quotient.mk_algebraMap K (I := curveChartYIdeal K) a).symm
  rw [hmk]
  simp [beta, betaPoly, MvPolynomial.eval₂Hom_C]

/-- `phi` acts on constants through the `K`-algebra structure of `A1 K`. -/
theorem phi_comp_algebraMap_K (K : Type) [Field K] :
    (phi K).comp (algebraMap K (A0 K)) = algebraMap K (A1 K) := by
  rw [← algebraMap_comp_algebraMap_R0, ← RingHom.comp_assoc, phi_comp_algebraMap_R0,
    alpha_comp_algebraMap_K]

/-! ## 5. Compatibility of the transition isomorphism with the structure maps -/

/-- The transition isomorphism is compatible with the structure morphisms over
`Spec K`: both composites from the chart-Z overlap to `Spec K` agree. -/
theorem curveChartOverlapTransitionIso_structure_compat (K : Type) [Field K] :
    (curveChartOverlapTransitionIso K).hom ≫ curveChartYOverlapMap K ≫
        curveChartYStructureMap K =
      curveChartZOverlapMap K ≫ curveSchemeStructureMap K := by
  have h : ((psi K).comp (algebraMap (R1 K) (A1 K))).comp (algebraMap K (R1 K)) =
      (algebraMap (R0 K) (A0 K)).comp (algebraMap K (R0 K)) := by
    rw [psi_comp_algebraMap_R1, beta_comp_algebraMap_K, algebraMap_comp_algebraMap_R0]
  rw [curveChartOverlapTransitionIso_hom, curveChartYOverlapMap_eq,
    curveChartYStructureMap_eq, curveChartZOverlapMap_eq, curveSchemeStructureMap_eq]
  rw [specMap_comp_three, ← Spec.map_comp]
  exact congrArg Spec.map (by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom h)

/-- The inverse of the transition isomorphism is compatible with the structure
morphisms over `Spec K`: both composites from the chart-Y overlap to `Spec K`
agree. -/
theorem curveChartOverlapTransitionIso_structure_compat_inv (K : Type) [Field K] :
    (curveChartOverlapTransitionIso K).inv ≫ curveChartZOverlapMap K ≫
        curveSchemeStructureMap K =
      curveChartYOverlapMap K ≫ curveChartYStructureMap K := by
  have h : ((phi K).comp (algebraMap (R0 K) (A0 K))).comp (algebraMap K (R0 K)) =
      (algebraMap (R1 K) (A1 K)).comp (algebraMap K (R1 K)) := by
    rw [phi_comp_algebraMap_R0, alpha_comp_algebraMap_K, algebraMap_comp_algebraMap_R1]
  rw [curveChartOverlapTransitionIso_inv, curveChartZOverlapMap_eq,
    curveSchemeStructureMap_eq, curveChartYOverlapMap_eq, curveChartYStructureMap_eq]
  rw [specMap_comp_three, ← Spec.map_comp]
  exact congrArg Spec.map (by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom h)


instance curveChartZOverlapMap_isOpenImmersion (K : Type) [Field K] :
    IsOpenImmersion (curveChartZOverlapMap K) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway
    (R := CommRingCat.of (curveCoordinateRing K)) (curveY K)

instance curveChartYOverlapMap_isOpenImmersion (K : Type) [Field K] :
    IsOpenImmersion (curveChartYOverlapMap K) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway
    (R := CommRingCat.of (curveChartYRing K))
    (Ideal.Quotient.mk (curveChartYIdeal K) (MvPolynomial.X 1))

noncomputable abbrev curveProjectiveChart (K : Type) [Field K] : Bool → Scheme
  | false => curveScheme K
  | true => curveChartYScheme K

noncomputable abbrev curveProjectiveOverlap (K : Type) [Field K] : Bool → Scheme
  | false => curveChartZOverlap K
  | true => curveChartYOverlap K

noncomputable def curveProjectiveGlueMap (K : Type) [Field K] (i j : Bool) (h : i ≠ j) :
    curveProjectiveOverlap K i ⟶ curveProjectiveChart K i := by
  cases i
  · exact curveChartZOverlapMap K
  · exact curveChartYOverlapMap K

/-- The symmetry inverse used in the cocycle case of the explicit two-chart glue
data. -/
theorem pullbackSymmetry_fst_inv_snd {A B Cc : Scheme} (f : A ⟶ Cc) (g : B ⟶ Cc)
    [IsIso f] [HasPullback f g] [HasPullback g f] :
    pullback.fst g f ≫ inv (pullback.snd f g) ≫ (pullbackSymmetry f g).hom =
      𝟙 (pullback g f) := by
  let S := pullbackSymmetry f g
  have h1 : S.hom ≫ pullback.fst g f = pullback.snd f g := by
    simpa [S] using pullbackSymmetry_hom_comp_fst f g
  have h2 : S.hom ≫ (pullback.fst g f ≫ inv (pullback.snd f g)) =
      𝟙 (pullback f g) := by
    rw [← Category.assoc, h1, IsIso.hom_inv_id]
  have h3 : pullback.fst g f ≫ inv (pullback.snd f g) = S.inv := by
    have h := IsIso.eq_inv_of_hom_inv_id h2
    simpa [S] using h
  rw [← Category.assoc, h3]
  exact S.inv_hom_id

/-- The two chart objects of the explicit glue data, indexed by `Bool`. -/
noncomputable abbrev curveProjectiveGlueU (K : Type) [Field K] : Bool → Scheme
  | false => curveScheme K
  | true => curveChartYScheme K

/-- The overlap objects of the explicit glue data, including the diagonal charts. -/
noncomputable abbrev curveProjectiveGlueV (K : Type) [Field K] : Bool × Bool → Scheme
  | (false, false) => curveScheme K
  | (false, true) => curveChartZOverlap K
  | (true, false) => curveChartYOverlap K
  | (true, true) => curveChartYScheme K

/-- The open immersions from the overlaps into the charts. -/
noncomputable abbrev curveProjectiveGlueF (K : Type) [Field K] :
    (i j : Bool) → curveProjectiveGlueV K (i, j) ⟶ curveProjectiveGlueU K i
  | false, false => 𝟙 (curveScheme K)
  | false, true => curveChartZOverlapMap K
  | true, false => curveChartYOverlapMap K
  | true, true => 𝟙 (curveChartYScheme K)

/-- The transition morphisms of the explicit glue data, built from an arbitrary
isomorphism `e` between the two overlaps. -/
noncomputable abbrev curveProjectiveGlueT (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    (i j : Bool) → curveProjectiveGlueV K (i, j) ⟶ curveProjectiveGlueV K (j, i)
  | false, false => 𝟙 (curveScheme K)
  | false, true => e.hom
  | true, false => e.inv
  | true, true => 𝟙 (curveChartYScheme K)

/-- The transition morphisms between the intersections of the explicit glue data. -/
noncomputable def curveProjectiveGlueTPrime (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) (i j k : Bool) :
    pullback (curveProjectiveGlueF K i j) (curveProjectiveGlueF K i k) ⟶
      pullback (curveProjectiveGlueF K j k) (curveProjectiveGlueF K j i) := by
  cases i <;> cases j <;> cases k
  · exact 𝟙 _
  · exact (pullbackSymmetry _ _).hom
  · exact pullback.fst _ _ ≫ curveProjectiveGlueT K e false true ≫
      inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ curveProjectiveGlueT K e false true ≫
      inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ curveProjectiveGlueT K e true false ≫
      inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ curveProjectiveGlueT K e true false ≫
      inv (pullback.snd _ _)
  · exact (pullbackSymmetry _ _).hom
  · exact 𝟙 _

/-- The explicit two-chart glue data with an arbitrary overlap transition
isomorphism `e`. -/
noncomputable abbrev curveProjectiveGlueDataWithTransition (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) : Scheme.GlueData where
  toGlueData :=
    { J := Bool
      U := curveProjectiveGlueU K
      V := curveProjectiveGlueV K
      f := curveProjectiveGlueF K
      f_mono i j := by
        cases i <;> cases j <;> dsimp only [curveProjectiveGlueF] <;> infer_instance
      f_hasPullback i j k := by
        cases i <;> cases j <;> cases k <;>
          dsimp only [curveProjectiveGlueF] <;> infer_instance
      f_id i := by
        cases i <;> dsimp only [curveProjectiveGlueF] <;> infer_instance
      t := curveProjectiveGlueT K e
      t_id i := by cases i <;> rfl
      t' := curveProjectiveGlueTPrime K e
      t_fac i j k := by
        cases i <;> cases j <;> cases k <;>
          simp [curveProjectiveGlueTPrime, curveProjectiveGlueT, curveProjectiveGlueF,
            curveProjectiveGlueU, curveProjectiveGlueV, fst_eq_snd_of_mono_eq,
            pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst, Category.assoc]
      cocycle i j k := by
        cases i <;> cases j <;> cases k <;>
          simp [curveProjectiveGlueTPrime, curveProjectiveGlueT, curveProjectiveGlueF,
            curveProjectiveGlueU, curveProjectiveGlueV, fst_eq_snd_of_mono_eq,
            pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst,
            pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd,
            pullbackSymmetry_fst_inv_snd, IsIso.inv_hom_id, e.hom_inv_id, e.inv_hom_id,
            Category.assoc, pullback.condition_assoc] }
  f_open i j := by
    dsimp only [curveProjectiveGlueF]
    cases i <;> cases j
    · exact inferInstance
    · exact inferInstance
    · exact inferInstance
    · exact inferInstance

/-- The actual two-chart glue data of the projective closure, with the transition
isomorphism `curveChartOverlapTransitionIso`. -/
noncomputable abbrev curveProjectiveSchemeGlueData (K : Type) [Field K] :
    Scheme.GlueData :=
  curveProjectiveGlueDataWithTransition K (curveChartOverlapTransitionIso K)

noncomputable abbrev curveProjectiveGluedScheme (K : Type) [Field K] : Scheme :=
  (curveProjectiveSchemeGlueData K).glued

noncomputable abbrev curveProjectiveChartZMap (K : Type) [Field K] :
    curveScheme K ⟶ curveProjectiveGluedScheme K :=
  (curveProjectiveSchemeGlueData K).ι false

instance curveProjectiveChartZMap_isOpenImmersion (K : Type) [Field K] :
    IsOpenImmersion (curveProjectiveChartZMap K) :=
  (curveProjectiveSchemeGlueData K).ι_isOpenImmersion false

noncomputable abbrev curveProjectiveChartYMap (K : Type) [Field K] :
    curveChartYScheme K ⟶ curveProjectiveGluedScheme K :=
  (curveProjectiveSchemeGlueData K).ι true

instance curveProjectiveChartYMap_isOpenImmersion (K : Type) [Field K] :
    IsOpenImmersion (curveProjectiveChartYMap K) :=
  (curveProjectiveSchemeGlueData K).ι_isOpenImmersion true

noncomputable abbrev curveProjectivePointAtInfinity (K : Type) [Field K] :
    curveProjectiveGluedScheme K :=
  curveProjectiveChartYMap K (curveInfinityPoint K)


theorem curveProjectiveGlueData_t_false_true (K : Type) [Field K] :
    (curveProjectiveSchemeGlueData K).t false true =
      (curveChartOverlapTransitionIso K).hom := rfl

theorem curveProjectivePointAtInfinity_eq (K : Type) [Field K] :
    curveProjectivePointAtInfinity K =
      curveProjectiveChartYMap K (curveInfinityPoint K) := rfl

theorem curveProjectiveCharts_jointly_surjective (K : Type) [Field K]
    (x : curveProjectiveGluedScheme K) :
    (∃ y, curveProjectiveChartZMap K y = x) ∨
      (∃ y, curveProjectiveChartYMap K y = x) := by
  obtain ⟨i, y, hy⟩ := (curveProjectiveSchemeGlueData K).openCover.exists_eq x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

open CategoryTheory.Limits

/-! ## 6. The off-diagonal gluing maps of the two-chart glue data

The glue data `curveProjectiveSchemeGlueData` is built explicitly from the two
charts and their overlap; these lemmas record the actual off-diagonal open
immersions and transition morphisms so that the structure morphism over `Spec K`
can be assembled from the two chart structure morphisms. -/

/-- The off-diagonal gluing morphism `V (false, true) ⟶ U false` is the overlap
open immersion into the chart `Z = 1`. -/
theorem curveProjectiveSchemeGlueData_f_false_true (K : Type) [Field K] :
    (curveProjectiveSchemeGlueData K).f false true = curveChartZOverlapMap K := rfl

/-- The off-diagonal gluing morphism `V (true, false) ⟶ U true` is the overlap
open immersion into the chart `Y = 1`. -/
theorem curveProjectiveSchemeGlueData_f_true_false (K : Type) [Field K] :
    (curveProjectiveSchemeGlueData K).f true false = curveChartYOverlapMap K := rfl

/-- The transition morphism `V (false, true) ⟶ V (true, false)` is the forward
overlap transition isomorphism. -/
theorem curveProjectiveSchemeGlueData_t_false_true (K : Type) [Field K] :
    (curveProjectiveSchemeGlueData K).t false true =
      (curveChartOverlapTransitionIso K).hom := rfl

/-- The transition morphism `V (true, false) ⟶ V (false, true)` is the inverse
overlap transition isomorphism. -/
theorem curveProjectiveSchemeGlueData_t_true_false (K : Type) [Field K] :
    (curveProjectiveSchemeGlueData K).t true false =
      (curveChartOverlapTransitionIso K).inv := rfl

/-! ## 7. The structure morphism of the projective closure over `Spec K` -/

/-- The family of chart structure morphisms over `Spec K`, indexed by the two
charts. -/
noncomputable def curveProjectiveChartStructureMap (K : Type) [Field K] (b : Bool) :
    curveProjectiveChart K b ⟶ Spec (CommRingCat.of K) :=
  match b with
  | false => curveSchemeStructureMap K
  | true => curveChartYStructureMap K

/-- The structure morphism of the glued projective closure over `Spec K`.  It is
assembled from the two chart structure morphisms by the multicoequalizer universal
property of the glue data: the compatibility on the overlap is exactly the
compatibility of the transition isomorphism with the structure morphisms proved in
Section 5. -/
noncomputable def curveProjectiveGluedStructureMap (K : Type) [Field K] :
    curveProjectiveGluedScheme K ⟶ Spec (CommRingCat.of K) := by
  classical
  haveI : HasMulticoequalizer (curveProjectiveSchemeGlueData K).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram (curveProjectiveSchemeGlueData K)
  refine Multicoequalizer.desc (curveProjectiveSchemeGlueData K).diagram
    (Spec (CommRingCat.of K)) (curveProjectiveChartStructureMap K) ?_
  rintro ⟨i, j⟩
  change (curveProjectiveSchemeGlueData K).f i j ≫
      curveProjectiveChartStructureMap K i =
    ((curveProjectiveSchemeGlueData K).t i j ≫
      (curveProjectiveSchemeGlueData K).f j i) ≫
      curveProjectiveChartStructureMap K j
  cases i <;> cases j
  · simp [curveProjectiveChartStructureMap]
  · rw [curveProjectiveSchemeGlueData_f_false_true K,
      curveProjectiveSchemeGlueData_t_false_true K,
      curveProjectiveSchemeGlueData_f_true_false K, Category.assoc]
    exact (curveChartOverlapTransitionIso_structure_compat K).symm
  · rw [curveProjectiveSchemeGlueData_f_true_false K,
      curveProjectiveSchemeGlueData_t_true_false K,
      curveProjectiveSchemeGlueData_f_false_true K, Category.assoc]
    exact (curveChartOverlapTransitionIso_structure_compat_inv K).symm
  · simp [curveProjectiveChartStructureMap]

/-- The structure morphism restricts to the chart-`Z` structure morphism
`curveSchemeStructureMap` on the first chart. -/
theorem curveProjectiveChartZMap_structureMap (K : Type) [Field K] :
    curveProjectiveChartZMap K ≫ curveProjectiveGluedStructureMap K =
      curveSchemeStructureMap K := by
  classical
  haveI : HasMulticoequalizer (curveProjectiveSchemeGlueData K).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram (curveProjectiveSchemeGlueData K)
  exact Multicoequalizer.π_desc (curveProjectiveSchemeGlueData K).diagram
    (Spec (CommRingCat.of K)) (curveProjectiveChartStructureMap K) _ false

/-- The structure morphism restricts to the chart-`Y` structure morphism
`curveChartYStructureMap` on the second chart. -/
theorem curveProjectiveChartYMap_structureMap (K : Type) [Field K] :
    curveProjectiveChartYMap K ≫ curveProjectiveGluedStructureMap K =
      curveChartYStructureMap K := by
  classical
  haveI : HasMulticoequalizer (curveProjectiveSchemeGlueData K).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram (curveProjectiveSchemeGlueData K)
  exact Multicoequalizer.π_desc (curveProjectiveSchemeGlueData K).diagram
    (Spec (CommRingCat.of K)) (curveProjectiveChartStructureMap K) _ true

/-- The structure morphism of the projective closure is the unique morphism whose
composites with the two chart open immersions are the two chart structure
morphisms. -/
theorem curveProjectiveGluedStructureMap_unique (K : Type) [Field K]
    (g : curveProjectiveGluedScheme K ⟶ Spec (CommRingCat.of K))
    (hZ : curveProjectiveChartZMap K ≫ g = curveSchemeStructureMap K)
    (hY : curveProjectiveChartYMap K ≫ g = curveChartYStructureMap K) :
    g = curveProjectiveGluedStructureMap K := by
  classical
  haveI : HasMulticoequalizer (curveProjectiveSchemeGlueData K).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram (curveProjectiveSchemeGlueData K)
  apply Multicoequalizer.hom_ext
  intro b
  cases b
  · change curveProjectiveChartZMap K ≫ g =
      curveProjectiveChartZMap K ≫ curveProjectiveGluedStructureMap K
    exact hZ.trans (curveProjectiveChartZMap_structureMap K).symm
  · change curveProjectiveChartYMap K ≫ g =
      curveProjectiveChartYMap K ≫ curveProjectiveGluedStructureMap K
    exact hY.trans (curveProjectiveChartYMap_structureMap K).symm

/-! ## 10. Realized cards

The transition isomorphism, the glue data, the glued scheme, the two chart open
immersions, the structure morphism over `Spec K` and the point at infinity are all
actual data constructed in this file.  They realize the frozen cards at universe 0
(the universe restriction is the one of the actual localisation construction in
Sections 7-9). -/

/-- The actual projective-closure transition and gluing package: the overlap
transition isomorphism, the two-chart glue data, the glued scheme, the two chart
open immersions, the structure morphism over `Spec K` and the point at infinity. -/
noncomputable def curveProjectiveClosureGlueCard (K : Type) [Field K] :
    CurveProjectiveClosureGlueCard K where
  transitionIso := curveChartOverlapTransitionIso K
  glueData := curveProjectiveSchemeGlueData K
  projectiveScheme := curveProjectiveGluedScheme K
  projectiveScheme_eq_glued := rfl
  chartZOpenImmersion := curveProjectiveChartZMap K
  chartZOpenImmersion_isOpenImmersion := curveProjectiveChartZMap_isOpenImmersion K
  chartYOpenImmersion := curveProjectiveChartYMap K
  chartYOpenImmersion_isOpenImmersion := curveProjectiveChartYMap_isOpenImmersion K
  structureMap := curveProjectiveGluedStructureMap K
  pointAtInfinity := curveProjectivePointAtInfinity K

/-- The frozen `CurveProjectiveClosureGlueCard` is realized by the actual gluing
data at universe 0. -/
theorem curveProjectiveClosureGlueCardRealized (K : Type) [Field K] :
    CurveProjectiveClosureGlueCardRealized K :=
  ⟨curveProjectiveClosureGlueCard K⟩

/-- The actual projective closure as an inhabitant of the frozen
`CurveProjectiveClosureCard` from `Example36CurveScheme`: the glued projective
scheme, its structure map over `Spec K`, the chart `Z = 1` as the affine open, the
identity comparison with `curveScheme K` and the point at infinity. -/
noncomputable def curveProjectiveClosureCard (K : Type) [Field K] :
    CurveProjectiveClosureCard K where
  projectiveScheme := curveProjectiveGluedScheme K
  projectiveStructureMap := curveProjectiveGluedStructureMap K
  affineOpen := curveScheme K
  affineOpenMap := curveProjectiveChartZMap K
  affineOpenMap_isOpenImmersion := curveProjectiveChartZMap_isOpenImmersion K
  affineIso := Iso.refl (curveScheme K)
  pointAtInfinity := curveProjectivePointAtInfinity K

/-- The frozen `CurveProjectiveClosureCard` of `Example36CurveScheme` is realized
by the actual gluing construction at universe 0. -/
theorem curveProjectiveClosureCardRealized (K : Type) [Field K] :
    CurveProjectiveClosureCardRealized K :=
  ⟨curveProjectiveClosureCard K⟩

/-- The comparison package of the projective closure is realized at universe 0. -/
theorem curveProjectiveClosureRemainingComparison_actual (K : Type) [Field K] :
    curveProjectiveClosureRemainingComparison K :=
  curveProjectiveClosureGlueCardRealized K

/-- The `CurveProjectiveClosureCard` fields are realized at universe 0. -/
theorem curveProjectiveClosureCardRemainingFields_actual (K : Type) [Field K] :
    curveProjectiveClosureCardRemainingFields K :=
  curveProjectiveClosureCardRealized K

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
