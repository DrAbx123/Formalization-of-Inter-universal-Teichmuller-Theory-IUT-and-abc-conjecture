/-
Probe for S1801: constant pseudofunctors and strong transformations.
-/
import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans

namespace S1801Probe

universe u

/-- The constant pseudofunctor at a category. -/
def constPseudo (F : Type u) [Field F] (C : Type u) [Category* C] :
    EtaleStackPseudofunctor F :=
  (Functor.const (SchemeOverField F)ᵒᵖ (Cat.of C)).toPseudofunctor'

#check constPseudo

/-- A base object. -/
def baseObj (F : Type u) [Field F] : LocallyDiscrete (SchemeOverField F)ᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op (Over.mk (𝟙 (Spec F))))

#check baseObj

end S1801Probe
