/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Finite-place family of model Frobenioids

The concrete finite-stage model Frobenioid of each finite place, packaged as
a presentation-valued family.  This is a self-contained instance of the
family part of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- A family of Frobenioid presentations. -/
structure PresentationFamily (iota : Type u) where
  presentation : iota -> FrobenioidPresentation.{u}

namespace PresentationFamily

variable {iota : Type u}

def baseCategory (family : PresentationFamily iota) (index : iota) :
    CategoryTheory.Cat.{u, u} :=
  (family.presentation index).baseCategory

noncomputable def presentation_axioms (family : PresentationFamily iota) (index : iota) :
    (family.presentation index).preFrobenioid.FrobenioidAxioms :=
  (family.presentation index).axioms

end PresentationFamily

/-- The finite-place family of concrete stage-model Frobenioids. -/
noncomputable def stageModelFamily :
    PresentationFamily (NumberField.FinitePlace K) where
  presentation := fun place =>
    SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation place

#check PresentationFamily
#check stageModelFamily

end SourceFrobenioidSystem
end Iut
