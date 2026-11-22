/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Minimal system of Frobenioids

IUTchI, Theorem A and Definition 6.13, (i), associate to initial Theta-data a
system of Frobenioids, whose associated D-Theta+-ellNF-Hodge theater is the
system of base categories.

This file lands only the minimal family part of that system: an index type,
an actual `FrobenioidPresentation` for each index, and the induced family of
base categories.  Gluing isomorphisms and the Theta+-ellNF poly-action are
deliberately not asserted here.  There are no arbitrary Prop fields.
-/

open CategoryTheory

namespace Iut

universe u

/-- Minimal family of Frobenioid presentations. -/
structure FrobenioidSystem (iota : Type u) where
  presentation : iota -> FrobenioidPresentation.{u}

namespace FrobenioidSystem

variable {iota : Type u}

/-- The base-category family of a system of Frobenioids. -/
def baseCategory (system : FrobenioidSystem iota) (index : iota) :
    CategoryTheory.Cat.{u, u} :=
  (system.presentation index).baseCategory

theorem baseCategory_isConnected (system : FrobenioidSystem iota) (index : iota) :
    CategoryTheory.IsConnected (system.baseCategory index) :=
  (system.presentation index).baseConnected

def presentation_axioms (system : FrobenioidSystem iota) (index : iota) :
    (system.presentation index).preFrobenioid.FrobenioidAxioms :=
  (system.presentation index).axioms

end FrobenioidSystem

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- The finite-place family of the concrete finite-stage model Frobenioids. -/
noncomputable def stageModelFrobenioidSystem :
    FrobenioidSystem (NumberField.FinitePlace K) where
  presentation := fun place =>
    SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation place

/-- Its base-category family. -/
noncomputable def stageModelBaseCategoryFamily :
    NumberField.FinitePlace K -> CategoryTheory.Cat.{u, u} :=
  fun place => (stageModelFrobenioidSystem (K := K)).baseCategory place

#check FrobenioidSystem
#check FrobenioidSystem.baseCategory
#check SourceFrobenioidSystem.stageModelFrobenioidSystem
#check SourceFrobenioidSystem.stageModelBaseCategoryFamily

end SourceFrobenioidSystem
end Iut
