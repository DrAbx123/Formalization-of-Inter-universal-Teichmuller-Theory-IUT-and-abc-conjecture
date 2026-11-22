/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Gluing data for the place/label model family

A data-level gluing structure on the place/label model family: a relation on
indices and an actual categorical equivalence of base categories for each
related pair.  This is the minimal self-contained counterpart of the full
poly-isomorphism gluing in IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Equivalence of base categories induced by equality of Cat objects. -/
noncomputable def eqToEquivalenceCat
    {C D : CategoryTheory.Cat.{u, u}} (h : C = D) : C ≌ D := by
  cases h
  exact CategoryTheory.Equivalence.refl

/-- Gluing data for the place/label model family. -/
structure StageModelGluingData (Label : Type u) where
  relation :
    (NumberField.FinitePlace K × Label) ->
      (NumberField.FinitePlace K × Label) -> Prop
  equivalence :
    forall {source target : NumberField.FinitePlace K × Label},
      relation source target ->
        CategoryTheory.Equivalence
          (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation
            source.1).baseCategory
          (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation
            target.1).baseCategory

namespace StageModelGluingData

/-- Trivial gluing: every pair related, by identity equivalences. -/
noncomputable def trivial (Label : Type u) :
    StageModelGluingData (K := K) Label where
  relation := fun source target => source = target
  equivalence := fun {source target} related =>
    eqToEquivalenceCat
      (congrArg
        (fun index =>
          (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation
            index.1).baseCategory) related)

end StageModelGluingData

#check StageModelGluingData
#check StageModelGluingData.trivial

end SourceFrobenioidSystem
end Iut
