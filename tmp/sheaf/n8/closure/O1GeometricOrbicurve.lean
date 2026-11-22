import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import Iut.Foundations.Orbicurve
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# O1 geometric orbicurve attempt

Actual geometric fiber: the representable etale pseudofunctor attached to the
affine Weierstrass scheme of Mathlib's ofJ0 curve over F.

What is constructed:
- an actual SchemeOverField F from a concrete WeierstrassCurve F;
- the actual representable etale pseudofunctor;
- a nonempty fiber object at the scheme itself;
- a conditional HyperbolicOrbicurve wrapper carrying the once-punctured
  elliptic signature.

What is NOT closed:
- IsStack for the representable pseudofunctor.  Mathlib provides the
  representable-sheaf theorem for a presheaf of types
  (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable), but no bridge
  from a sheaf of types to Pseudofunctor.IsStack for the associated discrete
  category pseudofunctor.  That bridge is the exact missing mathlib theorem.
- The affine Weierstrass scheme is the affine equation scheme, not the full
  once-punctured projective elliptic curve; the puncture and the geometric
  genus/puncture certificate are not constructed.
- The hyperbolic signature in realizedHyperbolicOrbicurve is inserted as
  metadata, not realized by a geometric OrbicurveGeometry construction.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation CategoryTheory.Bicategory

namespace LeanFormal.IUT.N8Closure.O1GeometricOrbicurve

universe u

variable (F : Type u) [Field F]

/-- The affine Weierstrass equation scheme as a scheme over Spec F. -/
noncomputable def affineWeierstrassScheme (W : WeierstrassCurve F) :
    Iut.SchemeOverField F :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap F W.toAffine.CoordinateRing)))

/-- Concrete Mathlib Weierstrass curve used for the geometric fiber. -/
noncomputable def o1WeierstrassCurve : WeierstrassCurve F :=
  WeierstrassCurve.ofJ0 F

/-- Optional elliptic instance: ofJ0 is elliptic when 3 is a unit. -/
theorem o1WeierstrassCurve_isElliptic [Fact (IsUnit (3 : F))] :
    (o1WeierstrassCurve F).IsElliptic := by
  change (WeierstrassCurve.ofJ0 F).IsElliptic
  infer_instance

/-- Actual geometric base scheme over F. -/
noncomputable def o1GeometricScheme : Iut.SchemeOverField F :=
  affineWeierstrassScheme F (o1WeierstrassCurve F)

/-- Actual representable etale pseudofunctor of the geometric scheme. -/
noncomputable def o1GeometricFiber : Iut.EtaleStackPseudofunctor F :=
  Iut.schemeRepresentableEtalePseudofunctor F (o1GeometricScheme F)

/-- The geometric fiber is nonempty at the scheme itself (identity point). -/
theorem o1GeometricFiber_obj_nonempty :
    Nonempty ((o1GeometricFiber F).obj
      (LocallyDiscrete.mk (Opposite.op (o1GeometricScheme F)))) :=
  ⟨Discrete.mk (𝟙 (o1GeometricScheme F))⟩

/-- Exact missing mathlib theorem: every representable etale pseudofunctor is
a stack.  The representable sheaf theorem for types exists; the discrete-
category stack bridge does not. -/
def RepresentableEtaleStackIsStack (X : Iut.SchemeOverField F) : Prop :=
  (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
    (Iut.SchemeOverField.etaleTopology F)

def MissingRepresentableStackBridge : Prop :=
  ∀ X : Iut.SchemeOverField F, RepresentableEtaleStackIsStack (F := F) X

/-- Conditional realized hyperbolic orbicurve from the actual geometric fiber. -/
noncomputable def o1RealizedGeometricOrbicurve
    (hStack : RepresentableEtaleStackIsStack (F := F) (o1GeometricScheme F)) :
    Iut.HyperbolicOrbicurve F :=
  realizedHyperbolicOrbicurve F (o1GeometricFiber F) hStack
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

theorem o1RealizedGeometricOrbicurve_signature
    (hStack : RepresentableEtaleStackIsStack (F := F) (o1GeometricScheme F)) :
    (o1RealizedGeometricOrbicurve (F := F) hStack).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  rfl

theorem o1RealizedGeometricOrbicurve_fiber
    (hStack : RepresentableEtaleStackIsStack (F := F) (o1GeometricScheme F)) :
    (o1RealizedGeometricOrbicurve (F := F) hStack).stack.fiber =
      o1GeometricFiber F :=
  rfl

end LeanFormal.IUT.N8Closure.O1GeometricOrbicurve

end