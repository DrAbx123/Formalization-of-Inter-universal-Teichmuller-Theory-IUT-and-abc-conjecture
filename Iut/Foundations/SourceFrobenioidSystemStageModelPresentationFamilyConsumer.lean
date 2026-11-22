/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Consumer: place/label presentation family of the finite-stage model

Projects the genuine Frobenioid presentation at each place/label index and
its Definition 1.3 axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelPresentationFamilyConsumer
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    FrobenioidPresentation.{u} :=
  SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation (K := K) index.1

@[simp] theorem stageModelPresentationFamilyConsumer_eq
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageModelPresentationFamilyConsumer (K := K) Label index =
      SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation (K := K) index.1 :=
  rfl

noncomputable def stageModelPresentationAxiomsConsumer
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (stageModelPresentationFamilyConsumer (K := K) Label index)
      |>.preFrobenioid.FrobenioidAxioms :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation (K := K) index.1).axioms

end SourceFrobenioidSystem
end Iut
