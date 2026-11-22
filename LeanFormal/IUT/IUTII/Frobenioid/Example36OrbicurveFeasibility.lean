import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import LeanFormal.IUT.IUTI.HodgeTheater.SourceEtaleStackInstanceSupplyReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31OrbicurveInstance
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# Feasibility of the nondegenerate once-punctured elliptic orbicurve (IUT I, Def. 3.1(b),(d))

This module records an investigation of whether a NON-degenerate once-punctured
elliptic-curve orbicurve / etale-stack instance can be built from the existing
tree APIs, and constructs the maximal actual geometric carrier that is available.

What is constructed (genuine geometry):

* the concrete elliptic curve y^2 = x^3 + 1 over Q (discriminant -432, hence
  elliptic), with two explicit rational points: the origin and (2,3);
* the concrete once-punctured curve: the curve above with the origin as its
  explicit projective puncture;
* the elliptic involution P |-> -P on the nonsingular projective points, as an
  additive equivalence of order two, fixing the puncture and acting nontrivially
  at the rational point (2,3); this is the geometric -1 involution whose
  stack-theoretic quotient is the relevant orbicurve; the quotient stack itself
  is NOT constructed (see below);
* the hyperbolic orbicurve signature (1; ;1) of a once-punctured elliptic curve
  and its hyperbolicity (Euler characteristic -1);
* a bundled OncePuncturedGeometricCarrier over Q collecting the curve, its
  puncture, the involution data and the signature.

Verdict on the etale-stack layer (the missing D6 construction):

The current foundation Iut.Foundations.Orbicurve offers the wrapper
HyperbolicOrbicurve F whose non-stack data is only an OrbicurveGeometry
certificate: a signature together with realizes_signature and hyperbolic.
realizedHyperbolicOrbicurve inserts that certificate into an arbitrary stack
fiber.  Consequences proved here:

* every HyperbolicOrbicurve F is definitionally obtained from its fiber and an
  inserted signature (hyperbolicOrbicurve_eq_signature_insertion), so the
  wrapper carries no curve data beyond the signature;
* the existing degenerate witnesses (sourceStackPointEtaleFiber,
  terminalConstantFiber) are point fibers: their value at every test scheme is a
  subsingleton category.  A point fiber cannot provide a surjection from its fiber
  objects at the base scheme onto the points of a genuine elliptic curve with at
  least two points (no_curvePointRealization_of_pointFiber), so it cannot be the
  geometric realization required for the source orbicurve;
* the current curve binding InitialThetaSource.SourceOncePuncturedGeometry
  stores only X.signature = sourceTypeOneOne: it never uses its curve argument
  and is satisfied by every curve once the signature equation holds
  (sourceBinding_vacuous).  Hence inserting the signature into the one-point
  fiber satisfies the current binding while carrying no geometric content; this
  is exactly the documented warning of SourceEtaleStackInstanceSupplyReduction.

Terminal conclusion: the current API does NOT construct a nondegenerate etale
stack fiber with curve content.  No construction from actual curve covers is
present (Mathlib has no etale-stack machinery for the Weierstrass model, and the
tree binds no geometric realization into EtaleStackOverField).  The exact
missing D6 construction is frozen as the structure MissingD6GeometricRealization:
a stack fiber with effective descent, a punctured elliptic curve, a
non-point-fiber (nondegeneracy) condition, and a surjective realization of the
curve's points by the fiber objects at the base scheme.  The existing witnesses
provably fail it.

What remains for Pi_v:

OncePuncturedPiVRemainder freezes the residual data needed for the profinite
fundamental group Pi_v of the once-punctured curve: the missing D6 geometric
realization; a HyperbolicOrbicurve with the once-punctured signature; the
stack-level sign action (OrbicurveSignAction); and the certified arithmetic /
geometric orbicurve group data (OrbicurveFundamentalGroupData), which yields the
exact sequences 1 -> geometric -> arithmetic -> Galois -> 1 and, with a cuspidal
decomposition, the boundary-cusp exact sequence.  None of these is constructed
or assumed here.

Boundary:

Only the local geometric carrier and the feasibility verdict of the D6 line are
formalized.  No fake etale stack, no fake orbicurve and no degenerate
substitution are introduced as the source object: the degenerate point fiber is
constructed solely as a witness that is proved NOT to be the source orbicurve.
No theta-pilot, q-pilot, Tate uniformization, Hodge-theater or source
identification is claimed.  The quotient stack C_F = X_F / (-1), the source
bad-reduction conditions, the scalar extensions and the cusp epsilon remain
unconstructed.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

universe u

/-! ## 1. The concrete elliptic curve y^2 = x^3 + 1 over Q -/

/-- The concrete Weierstrass curve y^2 = x^3 + 1 over Q (j-invariant 0). -/
def concreteEllipticCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 1

/-- The discriminant of the concrete curve: -16 * 27 = -432. -/
theorem concreteEllipticCurve_Δ : concreteEllipticCurve.Δ = -432 := by
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, concreteEllipticCurve]

/-- The concrete curve is elliptic: its discriminant -432 is a unit in Q. -/
theorem concreteEllipticCurve_isElliptic : concreteEllipticCurve.IsElliptic :=
  (WeierstrassCurve.isElliptic_iff concreteEllipticCurve).mpr (by
    rw [concreteEllipticCurve_Δ]; norm_num)

/-- The rational affine point (2,3) lies on y^2 = x^3 + 1 and is nonsingular. -/
theorem concreteAffineNonsingular_two_three :
    concreteEllipticCurve.toAffine.Nonsingular 2 3 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]
  norm_num [concreteEllipticCurve]

/-- The affine point (2,3) of the concrete curve. -/
def affinePointTwoThree : concreteEllipticCurve.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some 2 3 concreteAffineNonsingular_two_three

/-- The projective point [2 : 3 : 1] of the concrete curve. -/
def pointTwoThree : concreteEllipticCurve.toProjective.Point :=
  WeierstrassCurve.Projective.Point.fromAffine affinePointTwoThree

/-- (2,3) is not the origin: the puncture and (2,3) are distinct Q-points. -/
theorem pointTwoThree_ne_zero : pointTwoThree ≠ 0 :=
  WeierstrassCurve.Projective.Point.fromAffine_some_ne_zero concreteAffineNonsingular_two_three

/-- The underlying projective point class of (2,3) is [2 : 3 : 1]. -/
theorem pointTwoThree_point : pointTwoThree.point = ⟦![2, 3, 1]⟧ := by
  rw [pointTwoThree, affinePointTwoThree, WeierstrassCurve.Projective.Point.fromAffine_some,
    WeierstrassCurve.Projective.Point.mk_point]

/-- The underlying projective point class of -(2,3) is [2 : -3 : 1]. -/
theorem neg_pointTwoThree_point :
    (-pointTwoThree).point = ⟦![2, -3, 1]⟧ := by
  rw [WeierstrassCurve.Projective.Point.neg_point, pointTwoThree_point,
    WeierstrassCurve.Projective.negMap_eq]
  congr 1
  funext i
  fin_cases i <;>
    simp [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY_eq,
      concreteEllipticCurve]

/-- The elliptic involution is nontrivial at the rational point (2,3). -/
theorem pointTwoThree_ne_neg : pointTwoThree ≠ -pointTwoThree := by
  intro h
  have hpoint : (⟦![2, 3, 1]⟧ : WeierstrassCurve.Projective.PointClass ℚ) = ⟦![2, -3, 1]⟧ := by
    rw [← pointTwoThree_point, ← neg_pointTwoThree_point]
    exact congrArg (fun Q => Q.point) h
  have hne : (⟦![2, 3, 1]⟧ : WeierstrassCurve.Projective.PointClass ℚ) ≠ ⟦![2, -3, 1]⟧ := by
    intro heq
    have hq := Quotient.exact heq
    exact WeierstrassCurve.Projective.not_equiv_of_Y_ne (P := ![2, 3, 1]) (Q := ![2, -3, 1])
      (by
        simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two]
        norm_num) hq
  exact hne hpoint

/-- The concrete curve has at least two distinct Q-points (origin and (2,3)). -/
theorem concreteEllipticCurve_two_points :
    ∃ a b : concreteEllipticCurve.toProjective.Point, a ≠ b :=
  ⟨0, pointTwoThree, fun h => pointTwoThree_ne_zero h.symm⟩

/-! ## 2. The punctured curve, the -1 involution and the signature -/

/-- The concrete once-punctured elliptic curve: y^2 = x^3 + 1 punctured at the origin. -/
def concretePuncturedCurve : PuncturedEllipticCurve ℚ where
  curve := concreteEllipticCurve
  isElliptic := concreteEllipticCurve_isElliptic
  puncture := 0

/-- The elliptic involution P |-> -P on the projective points of a punctured curve. -/
def curveInvolution (E : PuncturedEllipticCurve ℚ) :
    E.curve.toProjective.Point → E.curve.toProjective.Point :=
  fun P => -P

/-- The involution is an involution. -/
theorem curveInvolution_involutive (E : PuncturedEllipticCurve ℚ) :
    Function.Involutive (curveInvolution E) :=
  fun P => neg_neg P

/-- The -1 involution is an additive automorphism of order two. -/
def curveInvolutionAddEquiv (E : PuncturedEllipticCurve ℚ) :
    E.curve.toProjective.Point ≃+ E.curve.toProjective.Point :=
  AddEquiv.neg _

/-- The automorphism -1 composed with itself is the identity. -/
theorem curveInvolutionAddEquiv_trans_self (E : PuncturedEllipticCurve ℚ) :
    (curveInvolutionAddEquiv E).trans (curveInvolutionAddEquiv E) = AddEquiv.refl _ := by
  ext P
  simp [curveInvolutionAddEquiv, AddEquiv.neg]

/-- The involution fixes the origin, hence acts on the punctured curve. -/
theorem curveInvolution_fixes_origin :
    curveInvolution concretePuncturedCurve concretePuncturedCurve.puncture =
      concretePuncturedCurve.puncture := by
  change -(0 : concreteEllipticCurve.toProjective.Point) = 0
  exact neg_zero

/-- The involution is nontrivial on the punctured curve's rational points. -/
theorem curveInvolution_nontrivial :
    curveInvolution concretePuncturedCurve pointTwoThree ≠ pointTwoThree := by
  simp only [curveInvolution]
  exact fun h => pointTwoThree_ne_neg h.symm

/-- The orbicurve signature of a once-punctured elliptic curve. -/
def oncePuncturedSignature : Iut.OrbicurveSignature :=
  Iut.OrbicurveSignature.oncePuncturedElliptic

/-- The once-punctured elliptic signature is hyperbolic. -/
theorem oncePuncturedSignature_hyperbolic : oncePuncturedSignature.IsHyperbolic :=
  Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

/-- Its orbifold Euler characteristic is -1. -/
theorem oncePuncturedSignature_eulerCharacteristic :
    oncePuncturedSignature.eulerCharacteristic = -1 :=
  Iut.OrbicurveSignature.oncePuncturedElliptic_eulerCharacteristic

/-- The once-punctured elliptic signature is exactly the current source
signature sourceTypeOneOne of SourceDefinition31Quantifiers. -/
theorem oncePuncturedElliptic_eq_sourceTypeOneOne :
    Iut.OrbicurveSignature.oncePuncturedElliptic = InitialThetaSource.sourceTypeOneOne := by
  ext <;> rfl

/-- The named signature of this file is the current source signature. -/
theorem oncePuncturedSignature_eq_sourceTypeOneOne :
    oncePuncturedSignature = InitialThetaSource.sourceTypeOneOne :=
  oncePuncturedElliptic_eq_sourceTypeOneOne

/-- A bundled once-punctured elliptic geometric carrier: actual curve, puncture,
-1 involution with its laws, and the hyperbolic signature. -/
structure OncePuncturedGeometricCarrier (F : Type u) [Field F] where
  /-- The actual punctured elliptic curve. -/
  curve : PuncturedEllipticCurve F
  /-- The elliptic -1 involution as an additive automorphism. -/
  involution : curve.curve.toProjective.Point ≃+ curve.curve.toProjective.Point
  /-- The involution is the negation of the group law. -/
  involution_eq_neg : ∀ P, involution P = -P
  /-- The involution fixes the puncture. -/
  fixes_puncture : involution curve.puncture = curve.puncture
  /-- The source orbicurve signature. -/
  signature : Iut.OrbicurveSignature
  /-- The signature is the once-punctured elliptic one. -/
  signature_eq : signature = Iut.OrbicurveSignature.oncePuncturedElliptic
  /-- The signature is hyperbolic. -/
  hyperbolic : signature.IsHyperbolic

/-- The concrete carrier over Q built from y^2 = x^3 + 1. -/
def concreteCarrier : OncePuncturedGeometricCarrier ℚ where
  curve := concretePuncturedCurve
  involution := curveInvolutionAddEquiv concretePuncturedCurve
  involution_eq_neg := fun _ => rfl
  fixes_puncture := curveInvolution_fixes_origin
  signature := oncePuncturedSignature
  signature_eq := rfl
  hyperbolic := oncePuncturedSignature_hyperbolic

/-- The concrete carrier really has the once-punctured elliptic signature. -/
theorem concreteCarrier_signature :
    concreteCarrier.signature = Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

/-- Base change of the concrete punctured curve to any field extension of Q
(for example C); the puncture and the elliptic-curve structure are transported. -/
def baseChangedPuncturedCurve (K : Type u) [Field K] [Algebra ℚ K] :
    PuncturedEllipticCurve K :=
  concretePuncturedCurve.baseChange K

/-! ## 3. What the current etale-stack API supplies, and the missing D6 data -/

open CategoryTheory
open AlgebraicGeometry
open scoped SpecOfNotation

/-- The base object id : Spec F -> Spec F of the etale site of schemes over F. -/
def baseSchemeObject (F : Type u) [Field F] : Iut.SchemeOverField F :=
  Over.mk (𝟙 (Spec(F)))

/-- A stack fiber is a point fiber when its value at every test scheme is a
subsingleton category: it carries no geometric points, no curve and no cover
data.  This is the precise degeneracy of the one-point witnesses. -/
def IsPointFiber {F : Type u} [Field F] (fiber : Iut.EtaleStackPseudofunctor F) : Prop :=
  ∀ U : (Iut.SchemeOverField F)ᵒᵖ, Subsingleton (fiber.obj (LocallyDiscrete.mk U))

/-- The one-point constant fiber of SourceEtaleStackInstanceSupplyReduction is
a point fiber. -/
theorem sourceStackPoint_isPointFiber (F : Type u) [Field F] :
    IsPointFiber (LeanFormal.IUT.sourceStackPointEtaleFiber F) := by
  intro U
  change Subsingleton LeanFormal.IUT.SourceStackPointObj
  infer_instance

/-- The terminal constant fiber of SourceDefinition31OrbicurveInstance is a
point fiber. -/
theorem terminalConstant_isPointFiber (F : Type u) [Field F] :
    IsPointFiber
      (InitialThetaSource.Definition31OrbicurveInstance.terminalConstantFiber F) := by
  intro U
  change Subsingleton (Discrete PUnit)
  infer_instance

/-- A point fiber cannot realize the points of a curve with at least two points:
there is no surjection from a subsingleton type onto a two-element set. -/
theorem not_surjective_of_subsingleton {α β : Type*} [Subsingleton α]
    {a b : β} (hab : a ≠ b) (f : α → β) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨x, hx⟩ := hf a
  obtain ⟨y, hy⟩ := hf b
  exact hab (by rw [← hx, ← hy, Subsingleton.elim x y])

/-- A point fiber has no surjective realization of the points of a curve with at
least two points, at the base scheme. -/
theorem no_curvePointRealization_of_pointFiber {F : Type u} [Field F]
    {fiber : Iut.EtaleStackPseudofunctor F} (h : IsPointFiber fiber)
    {curve : PuncturedEllipticCurve F}
    (hpts : ∃ a b : curve.curve.toProjective.Point, a ≠ b) :
    ¬ ∃ f : fiber.obj (LocallyDiscrete.mk (Opposite.op (baseSchemeObject F))) →
        curve.curve.toProjective.Point, Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨a, b, hab⟩ := hpts
  haveI := h (Opposite.op (baseSchemeObject F))
  exact not_surjective_of_subsingleton hab f hf

/-- Every HyperbolicOrbicurve of the current API is obtained by inserting a
signature certificate into its stack fiber: the wrapper carries no curve data
beyond the signature. -/
theorem hyperbolicOrbicurve_eq_signature_insertion {F : Type u} [Field F]
    (X : Iut.HyperbolicOrbicurve F) :
    X = realizedHyperbolicOrbicurve F X.stack.fiber X.stack.isStack X.signature
      X.geometry.hyperbolic := by
  cases X with
  | mk stack geometry =>
    cases stack with
    | mk fiber isStack signature =>
      cases geometry with
      | mk sig realizes hyperbolic =>
        cases realizes
        rfl

/-- The exact missing D6 construction: a nondegenerate etale stack fiber with
effective descent, together with an actual punctured elliptic curve whose
projective points are realized surjectively by the fiber objects at the base
scheme.  No inhabitant is constructed anywhere in the tree. -/
structure MissingD6GeometricRealization (F : Type u) [Field F] where
  /-- The actual punctured elliptic curve X_F. -/
  curve : PuncturedEllipticCurve F
  /-- The etale stack fiber over F. -/
  fiber : Iut.EtaleStackPseudofunctor F
  /-- Effective descent for the big etale topology. -/
  isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology F)
  /-- The fiber is not a degenerate point fiber. -/
  nondegenerate : ¬ IsPointFiber fiber
  /-- The curve's projective points are realized by the fiber objects at the base. -/
  curvePointRealization :
    ∃ f : fiber.obj (LocallyDiscrete.mk (Opposite.op (baseSchemeObject F))) →
        curve.curve.toProjective.Point, Function.Surjective f

namespace MissingD6GeometricRealization

variable {F : Type u} [Field F]

/-- The D6 realization supplies the etale-stack instance, hence in particular
EtaleStackInstanceSupply; the converse fails (see the point-fiber obstruction). -/
theorem toEtaleStackInstanceSupply (D : MissingD6GeometricRealization F) :
    EtaleStackInstanceSupply F :=
  ⟨D.fiber, D.isStack⟩

/-- The fiber of a D6 realization is not a point fiber. -/
theorem fiber_not_pointFiber (D : MissingD6GeometricRealization F) :
    ¬ IsPointFiber D.fiber :=
  D.nondegenerate

/-- A D6 realization yields a hyperbolic orbicurve with the once-punctured
elliptic signature (the stack wrapper is signature insertion). -/
theorem exists_oncePuncturedHyperbolicOrbicurve (D : MissingD6GeometricRealization F) :
    ∃ X : Iut.HyperbolicOrbicurve F,
      X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic :=
  ⟨realizedHyperbolicOrbicurve F D.fiber D.isStack
      Iut.OrbicurveSignature.oncePuncturedElliptic
      Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic, rfl⟩

/-- The curve points of the D6 realization are surjectively realized by the fiber. -/
theorem curvePoints_surjective (D : MissingD6GeometricRealization F) :
    ∃ f : D.fiber.obj (LocallyDiscrete.mk (Opposite.op (baseSchemeObject F))) →
        D.curve.curve.toProjective.Point, Function.Surjective f :=
  D.curvePointRealization

end MissingD6GeometricRealization

/-- The degenerate point-fiber orbicurve: signature inserted into the one-point
constant fiber.  This is NOT the source orbicurve; it is used only negatively. -/
def degeneratePointFiberOrbicurve (F : Type u) [Field F] : Iut.HyperbolicOrbicurve F :=
  realizedHyperbolicOrbicurve F (LeanFormal.IUT.sourceStackPointEtaleFiber F)
    (LeanFormal.IUT.sourceStackPointEtaleFiber_isStack F)
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

/-- The degenerate witness has the inserted once-punctured elliptic signature. -/
@[simp] theorem degeneratePointFiberOrbicurve_signature (F : Type u) [Field F] :
    (degeneratePointFiberOrbicurve F).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic := by
  simp [degeneratePointFiberOrbicurve]

/-- Its underlying fiber is the one-point constant fiber. -/
@[simp] theorem degeneratePointFiberOrbicurve_stack_fiber (F : Type u) [Field F] :
    (degeneratePointFiberOrbicurve F).stack.fiber =
      LeanFormal.IUT.sourceStackPointEtaleFiber F := by
  simp [degeneratePointFiberOrbicurve]

/-- The degenerate witness is a point-fiber object, with no geometric content. -/
theorem degeneratePointFiberOrbicurve_isPointFiber (F : Type u) [Field F] :
    IsPointFiber (degeneratePointFiberOrbicurve F).stack.fiber := by
  rw [degeneratePointFiberOrbicurve_stack_fiber]
  exact sourceStackPoint_isPointFiber F

/-- No D6 geometric realization can use the one-point fiber: the required
nondegeneracy field is violated. -/
theorem no_missingD6Realization_with_sourceStackPointFiber (F : Type u) [Field F]
    (D : MissingD6GeometricRealization F) :
    D.fiber ≠ LeanFormal.IUT.sourceStackPointEtaleFiber F := by
  intro h
  apply D.nondegenerate
  rw [h]
  exact sourceStackPoint_isPointFiber F

/-- No D6 geometric realization can use the terminal constant fiber. -/
theorem no_missingD6Realization_with_terminalConstantFiber (F : Type u) [Field F]
    (D : MissingD6GeometricRealization F) :
    D.fiber ≠
      InitialThetaSource.Definition31OrbicurveInstance.terminalConstantFiber F := by
  intro h
  apply D.nondegenerate
  rw [h]
  exact terminalConstant_isPointFiber F

/-- The current curve binding SourceOncePuncturedGeometry is satisfied by any
hyperbolic orbicurve with the once-punctured signature, for EVERY curve: it
never inspects the curve argument. -/
theorem sourceBinding_vacuous (F : Type u) [Field F] (curve : PuncturedEllipticCurve F)
    (X : Iut.HyperbolicOrbicurve F)
    (hX : X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic) :
    Nonempty (InitialThetaSource.SourceOncePuncturedGeometry curve X) := by
  refine (sourceOncePuncturedGeometry_nonempty_iff_signature curve X).mpr ?_
  rw [hX, oncePuncturedElliptic_eq_sourceTypeOneOne]

/-- Consequently the degenerate one-point orbicurve satisfies the current curve
binding for every possible punctured elliptic curve. -/
theorem degeneratePointFiberOrbicurve_sourceBinding (F : Type u) [Field F]
    (curve : PuncturedEllipticCurve F) :
    Nonempty (InitialThetaSource.SourceOncePuncturedGeometry curve
      (degeneratePointFiberOrbicurve F)) :=
  sourceBinding_vacuous F curve _
    (degeneratePointFiberOrbicurve_signature F)

/-- The point fiber carries no surjective realization of the concrete curve's
points; this is the precise sense in which the degenerate witness is not the
source orbicurve. -/
theorem degeneratePointFiber_no_concreteCurveRealization :
    ¬ ∃ f : (LeanFormal.IUT.sourceStackPointEtaleFiber ℚ).obj
        (LocallyDiscrete.mk (Opposite.op (baseSchemeObject ℚ))) →
        concreteEllipticCurve.toProjective.Point, Function.Surjective f :=
  no_curvePointRealization_of_pointFiber (F := ℚ) (curve := concretePuncturedCurve)
    (sourceStackPoint_isPointFiber ℚ) concreteEllipticCurve_two_points

/-! ## 4. What remains for Pi_v of the once-punctured elliptic curve -/

/-- The residual data needed for the profinite fundamental group Pi_v of the
once-punctured elliptic curve.  Every field is currently unconstructed: the
nondegenerate D6 geometric realization, the stack-level sign action, and the
certified arithmetic/geometric orbicurve group data (yielding the exact
sequences). -/
structure OncePuncturedPiVRemainder (F : Type u) [Field F] where
  /-- The missing nondegenerate D6 geometric realization. -/
  realization : MissingD6GeometricRealization F
  /-- The hyperbolic orbicurve carrying Pi_v. -/
  X : Iut.HyperbolicOrbicurve F
  /-- Its signature is the once-punctured elliptic signature. -/
  X_signature : X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic
  /-- The Galois group of the base field. -/
  galois : ProfiniteGrp
  /-- The certified arithmetic/geometric fundamental-group data of X. -/
  groups : Iut.OrbicurveFundamentalGroupData X galois
  /-- The stack-level elliptic sign action. -/
  signAction : Iut.OrbicurveSignAction X

namespace OncePuncturedPiVRemainder

variable {F : Type u} [Field F]

/-- The Pi_v remainder supplies the geometric EtaleStackInstanceSupply. -/
theorem toEtaleStackInstanceSupply (D : OncePuncturedPiVRemainder F) :
    EtaleStackInstanceSupply F :=
  D.realization.toEtaleStackInstanceSupply

/-- The Pi_v remainder has a nondegenerate fiber. -/
theorem fiber_not_pointFiber (D : OncePuncturedPiVRemainder F) :
    ¬ IsPointFiber D.realization.fiber :=
  D.realization.nondegenerate

/-- The certified arithmetic fundamental group of the orbicurve. -/
theorem nonempty_arithmeticFundamentalGroup (D : OncePuncturedPiVRemainder F) :
    Nonempty (Iut.OrbicurveEtaleFundamentalGroup D.X D.groups.arithmeticGroup) :=
  ⟨D.groups.arithmetic⟩

/-- The exact sequence 1 -> geometric -> arithmetic -> Galois attached to the
certified group data. -/
noncomputable def exactSequence (D : OncePuncturedPiVRemainder F) :
    Iut.ProfiniteFundamentalExactSequence D.groups.geometric.group
      D.groups.arithmetic.group D.galois :=
  Iut.OrbicurveFundamentalGroupData.exactSequence D.groups

/-- The Pi_v remainder cannot be built on the one-point degenerate fiber. -/
theorem realization_fiber_ne_sourceStackPointFiber (D : OncePuncturedPiVRemainder F) :
    D.realization.fiber ≠ LeanFormal.IUT.sourceStackPointEtaleFiber F :=
  no_missingD6Realization_with_sourceStackPointFiber F D.realization

end OncePuncturedPiVRemainder

end LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
