import tmp.sheaf.n8.closure.O1GeometricOrbicurve
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Subcanonical

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Constructed bridge target for representable etale stacks

Actual part:
- the big etale topology on Scheme is subcanonical (via
  etale <= proetale <= fpqc and the fpqc subcanonical instance);
- consequently every representable presheaf yoneda.obj X is a sheaf;
- the target bridge from Presheaf.IsSheaf to IsStack is stated exactly.

Missing mathlib lemma: a discrete-category pseudofunctor associated to a
sheaf of types is a stack.  Mathlib has the representable sheaf theorem but no
Presheaf.IsSheaf -> Pseudofunctor.IsStack bridge for the discrete category
pseudofunctor.  No arbitrary IsStack instance is introduced.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.N8Closure.O1GeometricOrbicurve
open scoped SpecOfNotation CategoryTheory.Bicategory

namespace LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed

universe u

variable (F : Type u) [Field F]

/-- The big etale topology on schemes is subcanonical. -/
noncomputable instance etaleTopologySubcanonical :
    AlgebraicGeometry.Scheme.etaleTopology.Subcanonical :=
  .of_le (le_trans
    AlgebraicGeometry.Scheme.etaleTopology_le_proetaleTopology
    AlgebraicGeometry.Scheme.proetaleTopology_le_fpqcTopology)

/-- Every representable etale presheaf is a sheaf. -/
theorem representableEtalePresheaf_isSheaf
    (X : Iut.SchemeOverField F) :
    Presheaf.IsSheaf (Iut.SchemeOverField.etaleTopology F)
      (yoneda.obj X) :=
  (isSheaf_iff_isSheaf_of_type (J := Iut.SchemeOverField.etaleTopology F) (yoneda.obj X)).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Iut.SchemeOverField.etaleTopology F) (yoneda.obj X))

/-- Exact missing bridge: sheaf of types -> stack of its discrete categories.
  The target is the representable etale pseudofunctor IsStack statement. -/
def RepresentableSheafToStackBridge : Prop :=
  ∀ X : Iut.SchemeOverField F,
    Presheaf.IsSheaf (Iut.SchemeOverField.etaleTopology F) (yoneda.obj X) →
      (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
        (Iut.SchemeOverField.etaleTopology F)

/-- Actual reduction: the bridge plus the actual representable sheaf theorem
yields IsStack for the representable fiber. -/
theorem representableFiber_isStack_of_bridge
    (hbridge : RepresentableSheafToStackBridge (F := F))
    (X : Iut.SchemeOverField F) :
    (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  hbridge X (representableEtalePresheaf_isSheaf (F := F) X)

/-- Conditional geometric orbicurve from the actual geometric scheme. -/
noncomputable def conditionalGeometricOrbicurve
    (hbridge : RepresentableSheafToStackBridge (F := F)) :
    Iut.HyperbolicOrbicurve F :=
  o1RealizedGeometricOrbicurve (F := F)
    (representableFiber_isStack_of_bridge (F := F) hbridge
      (o1GeometricScheme F))

theorem conditionalGeometricOrbicurve_signature
    (hbridge : RepresentableSheafToStackBridge (F := F)) :
    (conditionalGeometricOrbicurve (F := F) hbridge).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  rfl

/-- Exact gap statement: the missing bridge is not replaced by an instance. -/
def MissingRepresentableSheafToStackBridge : Prop :=
  ¬ RepresentableSheafToStackBridge (F := F)

end LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed

end