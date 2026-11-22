/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluing

/-!
# Consumer of the place/label system data with gluing

Unpacks `StageModelSystemDataGluing` into the actual system of Frobenioids,
its base-category family, its gluing relation/equivalences, and its label
action.  This is the consumer-facing form of the data of IUTchI, Definition
6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Consumer view of the place/label system data. -/
structure StageModelSystemDataGluingConsumer
    (Label : Type u) (G : Type u) [Group G] where
  data : StageModelSystemDataGluing (K := K) Label G

namespace StageModelSystemDataGluingConsumer

variable {Label : Type u} {G : Type u} [Group G]

/-- The actual Frobenioid presentation at an index. -/
def presentation (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    FrobenioidPresentation.{u} :=
  consumer.data.system.presentation index

/-- Its base category. -/
def baseCategory (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.Cat.{u, u} :=
  consumer.data.system.base index

/-- Base category is the presentation's base category. -/
@[simp] theorem baseCategory_eq
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    consumer.baseCategory index =
      (consumer.presentation index).baseCategory :=
  consumer.data.system.base_eq index

/-- The base category is connected. -/
theorem baseCategory_isConnected
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected (consumer.baseCategory index) :=
  consumer.data.system.base_connected index

/-- The presentation satisfies the full Frobenioid axioms. -/
noncomputable def presentation_axioms
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    (consumer.presentation index).preFrobenioid.FrobenioidAxioms :=
  consumer.data.system.axioms index

/-- The gluing relation carried by the data. -/
def gluingRelation
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (source target : NumberField.FinitePlace K × Label) : Prop :=
  consumer.data.gluing.relation source target

/-- Equivalence of categories induced by an equality of Cat objects. -/
private noncomputable def eqToEquivalenceCat
    {C D : CategoryTheory.Cat.{u, u}} (h : C = D) : C ≌ D := by
  cases h
  exact CategoryTheory.Equivalence.refl

/-- Transport a categorical equivalence along equalities of Cat objects. -/
private noncomputable def castEquivalence
    {C D C' D' : CategoryTheory.Cat.{u, u}}
    (e : CategoryTheory.Equivalence C D)
    (hC : C = C') (hD : D = D') :
    CategoryTheory.Equivalence C' D' :=
  (eqToEquivalenceCat hC.symm).trans
    (e.trans (eqToEquivalenceCat hD))
/-- The gluing equivalence carried by the data. -/
noncomputable def gluingEquivalence
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    {source target : NumberField.FinitePlace K × Label}
    (related : consumer.gluingRelation source target) :
    CategoryTheory.Equivalence (consumer.baseCategory source)
      (consumer.baseCategory target) :=
  castEquivalence
    (consumer.data.gluing.equivalence related)
    ((consumer.data.system.base_eq source).trans
      (consumer.data.compat source)).symm
    ((consumer.data.system.base_eq target).trans
      (consumer.data.compat target)).symm

/-- The label action carried by the data. -/
def labelAction (consumer : StageModelSystemDataGluingConsumer (K := K) Label G) :
    StageModelLabelActionData Label G :=
  consumer.data.labelAction

/-- Apply a label group element to a place/label index. -/
def applyLabel (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (g : G) (index : NumberField.FinitePlace K × Label) :
    NumberField.FinitePlace K × Label :=
  consumer.labelAction.apply g index

end StageModelSystemDataGluingConsumer

#check StageModelSystemDataGluingConsumer
#check StageModelSystemDataGluingConsumer.presentation
#check StageModelSystemDataGluingConsumer.baseCategory_isConnected
#check StageModelSystemDataGluingConsumer.gluingEquivalence

end SourceFrobenioidSystem
end Iut
