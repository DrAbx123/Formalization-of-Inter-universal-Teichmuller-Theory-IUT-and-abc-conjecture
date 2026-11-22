/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingSystemConsumer

/-!
# Consumer: base-category and axiom fields of place/label system data

Consumes the system+gluing consumer and exposes the base category and the
Definition 1.3 axiom package of each place/label component.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

/-- Base category of a component. -/
def baseCategory (data : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.Cat.{u, u} :=
  data.system.base index

/-- Base category is the presentation's base category. -/
@[simp] theorem baseCategory_eq
    (data : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    data.baseCategory index = (data.system.presentation index).baseCategory :=
  data.system.base_eq index

theorem baseCategory_isConnected
    (data : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected (data.baseCategory index) :=
  data.system.base_connected index

/-- The component Definition 1.3 axiom package. -/
noncomputable def axioms
    (data : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    (data.system.presentation index).preFrobenioid.FrobenioidAxioms :=
  data.system.axioms index

/-- The gluing equivalence carried by the data. -/
def gluingEquivalence
    (data : StageModelSystemDataGluing (K := K) Label G)
    {source target : NumberField.FinitePlace K × Label}
    (related : data.gluingRelation source target) :
    CategoryTheory.Equivalence (data.baseCategory source)
      (data.baseCategory target) :=
  data.gluing.equivalence related

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.baseCategory
#check StageModelSystemDataGluing.baseCategory_isConnected
#check StageModelSystemDataGluing.axioms

end SourceFrobenioidSystem
end Iut
