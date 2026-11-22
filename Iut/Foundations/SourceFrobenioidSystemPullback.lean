/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Pullback of a system of Frobenioids

Precomposition of the index type by a map.  Every component remains a
genuine Frobenioid presentation, with its full Frobenioid axioms.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota iota' : Type u}

/-- Pull back a system along a map of index types. -/
def pullback (system : FrobenioidSystem iota) (map : iota' -> iota) :
    FrobenioidSystem iota' where
  presentation := fun index => system.presentation (map index)

@[simp] theorem pullback_presentation
    (system : FrobenioidSystem iota) (map : iota' -> iota) (index : iota') :
    (pullback system map).presentation index = system.presentation (map index) :=
  rfl

@[simp] theorem pullback_baseCategory
    (system : FrobenioidSystem iota) (map : iota' -> iota) (index : iota') :
    (pullback system map).baseCategory index = system.baseCategory (map index) :=
  rfl

noncomputable def pullback_presentation_axioms
    (system : FrobenioidSystem iota) (map : iota' -> iota) (index : iota') :
    (pullback system map).presentation index |>.preFrobenioid.FrobenioidAxioms :=
  (system.presentation (map index)).axioms

end FrobenioidSystem

#check FrobenioidSystem.pullback
#check FrobenioidSystem.pullback_presentation_axioms

end Iut
