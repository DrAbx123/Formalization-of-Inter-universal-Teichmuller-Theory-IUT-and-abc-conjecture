import tmp.sheaf.n8.closure.RepresentableStackIsStackConstructed

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Representable sheaf to stack bridge: constructed part and exact gap

Actual construction:
- etale topology subcanonical;
- representable presheaf yoneda.obj X is a sheaf;
- the bridge target is exactly the IsStack assertion for representable fibers.

The descent-data equivalence itself is NOT constructed here.  The missing
mathlib lemma is the discrete-category descent bridge: a sheaf of types P
should give an IsStack pseudofunctor U |-> Discrete (P U).  Mathlib has the
sheaf condition for types but no category-valued descent equivalence packaging
it as Pseudofunctor.IsStack.  This file records the minimal bridge and its
exact equivalence to the desired IsStack statement; it introduces no arbitrary
instance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation CategoryTheory.Bicategory

namespace LeanFormal.IUT.N8Closure.RepresentableSheafToStackBridgeConstructed

universe u

variable (F : Type u) [Field F]

/-- Actual subcanonicality of the big etale topology. -/
noncomputable instance etaleTopologySubcanonical :
    AlgebraicGeometry.Scheme.etaleTopology.Subcanonical :=
  .of_le (le_trans
    AlgebraicGeometry.Scheme.etaleTopology_le_proetaleTopology
    AlgebraicGeometry.Scheme.proetaleTopology_le_fpqcTopology)

/-- Every representable etale presheaf is a sheaf (actual). -/
theorem representablePresheaf_isSheaf
    (X : Iut.SchemeOverField F) :
    Presheaf.IsSheaf (Iut.SchemeOverField.etaleTopology F)
      (yoneda.obj X) :=
  (isSheaf_iff_isSheaf_of_type
    (J := Iut.SchemeOverField.etaleTopology F) (yoneda.obj X)).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Iut.SchemeOverField.etaleTopology F) (yoneda.obj X))

/-- Minimal bridge: sheaf of types -> discrete-category stack. -/
def RepresentableSheafToStackBridge : Prop :=
  ∀ X : Iut.SchemeOverField F,
    Presheaf.IsSheaf (Iut.SchemeOverField.etaleTopology F) (yoneda.obj X) →
      (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
        (Iut.SchemeOverField.etaleTopology F)

/-- Exact equivalence: the bridge is precisely the universal IsStack statement
for representable fibers. -/
theorem representableFiberIsStack_universal_iff_bridge :
    (∀ X : Iut.SchemeOverField F,
      (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
        (Iut.SchemeOverField.etaleTopology F)) ↔
      RepresentableSheafToStackBridge (F := F) := by
  constructor
  · intro h X _
    exact h X
  · intro h X
    exact h X (representablePresheaf_isSheaf (F := F) X)

/-- Conditional actual IsStack for a representable fiber. -/
theorem representableFiber_isStack_of_bridge
    (h : RepresentableSheafToStackBridge (F := F))
    (X : Iut.SchemeOverField F) :
    (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  h X (representablePresheaf_isSheaf (F := F) X)

/-- Conditional geometric orbicurve via the actual geometric scheme. -/
noncomputable def conditionalGeometricOrbicurve
    (h : RepresentableSheafToStackBridge (F := F)) :
    Iut.HyperbolicOrbicurve F :=
  O1GeometricOrbicurve.o1RealizedGeometricOrbicurve (F := F)
    (representableFiber_isStack_of_bridge (F := F) h
      (O1GeometricOrbicurve.o1GeometricScheme F))

theorem conditionalGeometricOrbicurve_signature
    (h : RepresentableSheafToStackBridge (F := F)) :
    (conditionalGeometricOrbicurve (F := F) h).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  rfl

/-- Exact remaining mathlib lemma: no bridge from Presheaf.IsSheaf to
Pseudofunctor.IsStack for the associated discrete-category pseudofunctor. -/
def MissingDiscreteSheafToStackLemma : Prop :=
  ¬ RepresentableSheafToStackBridge (F := F)

end LeanFormal.IUT.N8Closure.RepresentableSheafToStackBridgeConstructed

end
