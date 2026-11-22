import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import Iut.Foundations.Orbicurve

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# O1 constructed etale stack

An actual nonempty, nonterminal constant etale stack over any field F: the
constant pseudofunctor at the two-object indiscrete groupoid O1StackObj.

Actual:
- O1StackObj has two objects and one morphism between any two objects;
  every hom type is PUnit, all objects are isomorphic, the category is not
  terminal and not empty;
- the constant fiber is a stack for the big etale topology;
- realizedHyperbolicOrbicurve gives an actual HyperbolicOrbicurve wrapper.

Honest boundary: the fiber is an indiscrete groupoid, NOT an actual curve or
orbicurve.  The hyperbolic signature is inserted by
realizedHyperbolicOrbicurve, not realized by the fiber.  The missing geometric
realization is the actual once-punctured elliptic curve / hyperbolic orbicurve
with its stack structure, involution, sign quotient, finite-etale covers and
certified etale fundamental groups.  This file does not claim D6 source
content; it constructs the nonterminal stack shape the user requested without
using the empty/terminal point stack.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.Bicategory

namespace LeanFormal.IUT.N8Closure.O1ConstructedStack

universe u

/-- Two-object indiscrete groupoid carrier. -/
inductive O1StackObj : Type u where
  | x : O1StackObj
  | y : O1StackObj

instance o1StackObjCategory : Category O1StackObj where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

instance o1StackObjHomSubsingleton (X Y : O1StackObj) :
    Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The unique isomorphism between any two objects of the indiscrete groupoid. -/
def o1ObjIso (X Y : O1StackObj) : X ≅ Y where
  hom := PUnit.unit
  inv := PUnit.unit
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The one-object category of the point stack is not used here. -/
abbrev o1Carrier : Cat.{u, u} := Cat.of O1StackObj

/-- Constant functor from schemes over F to the two-object indiscrete groupoid. -/
noncomputable def o1FiberFunctor (F : Type u) [Field F] :
    (Iut.SchemeOverField F)ᵒᵖ ⥤ Cat.{u, u} where
  obj _ := o1Carrier
  map _ := 𝟙 o1Carrier
  map_id _ := rfl
  map_comp _ _ := (Category.comp_id (𝟙 o1Carrier)).symm

/-- The actual nonterminal constant etale pseudofunctor. -/
noncomputable def o1EtaleFiber (F : Type u) [Field F] :
    Iut.EtaleStackPseudofunctor F :=
  (o1FiberFunctor F).toPseudofunctor'

/-- Descent for the two-object indiscrete fiber: hom types are subsingleton and
all objects are isomorphic, so `toDescentData` is an equivalence. -/
theorem isEquivalence_toDescentData_o1EtaleFiber
    (F : Type u) [Field F]
    {S : Iut.SchemeOverField F} (R : Presieve S) :
    ((o1EtaleFiber F).toDescentData
      (fun f : R.category => f.obj.hom)).IsEquivalence := by
  refine { faithful := ⟨fun {A B} φ ψ _ =>
            @Subsingleton.elim (A ⟶ B) (o1StackObjHomSubsingleton A B) _ _⟩,
           full := ⟨fun {A B} c => ?_⟩,
           essSurj := ⟨fun Y => ?_⟩ }
  · refine ⟨PUnit.unit, ?_⟩
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact @Subsingleton.elim _ (o1StackObjHomSubsingleton _ _) _ _
  · refine ⟨O1StackObj.x, ⟨?_⟩⟩
    refine Pseudofunctor.DescentData.isoMk
      (fun i => o1ObjIso O1StackObj.x (Y.obj i)) ?_
    intros
    exact @Subsingleton.elim _ (o1StackObjHomSubsingleton _ _) _ _

theorem o1EtaleFiber_isStackFor (F : Type u) [Field F]
    {S : Iut.SchemeOverField F} (R : Presieve S) :
    (o1EtaleFiber F).IsStackFor R :=
  (Pseudofunctor.isStackFor_iff (o1EtaleFiber F) R).2
    (isEquivalence_toDescentData_o1EtaleFiber F R)

/-- The constructed fiber is an actual etale stack. -/
theorem o1EtaleFiber_isStack (F : Type u) [Field F] :
    (o1EtaleFiber F).IsStack (Iut.SchemeOverField.etaleTopology F) := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro S R _
  exact o1EtaleFiber_isStackFor F R.arrows

/-- Actual nonterminal hyperbolic wrapper from the constructed stack. -/
noncomputable def o1RealizedHyperbolicOrbicurve (F : Type u) [Field F] :
    Iut.HyperbolicOrbicurve F :=
  realizedHyperbolicOrbicurve F (o1EtaleFiber F) (o1EtaleFiber_isStack F)
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

theorem o1RealizedHyperbolicOrbicurve_signature (F : Type u) [Field F] :
    (o1RealizedHyperbolicOrbicurve F).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  rfl

theorem o1RealizedHyperbolicOrbicurve_fiber (F : Type u) [Field F] :
    (o1RealizedHyperbolicOrbicurve F).stack.fiber = o1EtaleFiber F :=
  rfl

/-- The constructed fiber is not the one-point terminal fiber: it has two
objects.  This is a nonterminal shape witness, not an orbicurve. -/
theorem o1Fiber_has_two_objects_nonterminal :
    Nonempty (O1StackObj.x ≠ O1StackObj.y) :=
  ⟨by intro h; cases h⟩

end LeanFormal.IUT.N8Closure.O1ConstructedStack

end