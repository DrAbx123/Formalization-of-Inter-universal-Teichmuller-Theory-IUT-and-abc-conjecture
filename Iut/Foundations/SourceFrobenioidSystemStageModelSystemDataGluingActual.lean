/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingConsumerSystem

/-!
# Actual place/label system of Frobenioids with gluing and label action

Bundles the actual `FrobenioidSystem`, the data-level gluing relation and
equivalences, and the label poly-action.  This is the consumer-facing form of
IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

private noncomputable def castEquivalence
    {C D C' D' : CategoryTheory.Cat.{u, u}}
    (e : CategoryTheory.Equivalence C D)
    (hC : C = C') (hD : D = D') :
    CategoryTheory.Equivalence C' D' :=
  (eqToEquivalenceCat hC.symm).trans
    (e.trans (eqToEquivalenceCat hD))

structure StageModelSystemDataGluingActual (Label : Type u) (G : Type u) [Group G] where
  system : FrobenioidSystem (NumberField.FinitePlace K × Label)
  relation :
    (NumberField.FinitePlace K × Label) ->
      (NumberField.FinitePlace K × Label) -> Prop
  equivalence :
    forall {source target},
      relation source target ->
        CategoryTheory.Equivalence (system.baseCategory source)
          (system.baseCategory target)
  labelAction : G →* Equiv.Perm (NumberField.FinitePlace K × Label)

namespace StageModelSystemDataGluingActual

noncomputable def ofData
    {Label : Type u} {G : Type u} [Group G]
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G) :
    StageModelSystemDataGluingActual (K := K) Label G where
  system :=
    StageModelSystemDataGluingConsumer.toFrobenioidSystem consumer
  relation :=
    StageModelSystemDataGluingConsumer.gluingRelation consumer
  equivalence := fun {source target} related =>
    castEquivalence
      (StageModelSystemDataGluingConsumer.gluingEquivalence consumer related)
      (StageModelSystemDataGluingConsumer.toFrobenioidSystem_baseCategory
        consumer source).symm
      (StageModelSystemDataGluingConsumer.toFrobenioidSystem_baseCategory
        consumer target).symm
  labelAction :=
    { toFun := fun g =>
        Equiv.prodCongr (Equiv.refl _)
          ((StageModelSystemDataGluingConsumer.labelAction consumer).action g)
      map_one' := by
        apply Equiv.ext
        intro index
        rcases index with ⟨place, label⟩
        simp [Equiv.prodCongr, map_one]
      map_mul' := fun g h => by
        apply Equiv.ext
        intro index
        rcases index with ⟨place, label⟩
        simp [Equiv.prodCongr, Equiv.Perm.mul_apply, map_mul] }

end StageModelSystemDataGluingActual

#check StageModelSystemDataGluingActual
#check StageModelSystemDataGluingActual.ofData

end SourceFrobenioidSystem
end Iut
