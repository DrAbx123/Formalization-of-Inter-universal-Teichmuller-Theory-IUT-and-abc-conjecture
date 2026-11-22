/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingBaseConsumer

/-!
# Consumer: Frobenioid axioms of the concrete place/label system

Each component of the concrete finite-stage place/label system carries the
full Definition 1.3 axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
namespace StageModelSystemDataGluing

variable {Label : Type u} {G : Type u} [Group G]

noncomputable def ofFiniteStage_axioms
    (index : NumberField.FinitePlace K × Label) :
    ((ofFiniteStage (K := K) Label G).system.presentation index)
      |>.preFrobenioid.FrobenioidAxioms :=
  ((ofFiniteStage (K := K) Label G).system.presentation index).axioms

@[simp] theorem ofFiniteStage_axioms_eq
    (index : NumberField.FinitePlace K × Label) :
    ofFiniteStage_axioms (K := K) (Label := Label) (G := G) index =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1).axioms :=
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.ofFiniteStage_axioms
#check StageModelSystemDataGluing.ofFiniteStage_axioms_eq

end SourceFrobenioidSystem
end Iut
