/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemReindex
import Iut.Foundations.SourceFrobenioidSystemBaseCategory

/-!
# Reindexing preserves the Frobenioid axioms

Every component of a reindexed system is still a genuine
`FrobenioidPresentation`, with the same Frobenioid axioms and base category.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota iota' : Type u}

noncomputable def reindex_presentation_axioms
    (system : FrobenioidSystem iota) (map : iota' -> iota) (index : iota') :
    (system.reindex map).presentation index |>.preFrobenioid.FrobenioidAxioms :=
  (system.presentation (map index)).axioms

@[simp] theorem reindex_baseCategory
    (system : FrobenioidSystem iota) (map : iota' -> iota) (index : iota') :
    (system.reindex map).baseCategory index =
      system.baseCategory (map index) :=
  rfl

#check FrobenioidSystem.reindex_presentation_axioms
#check FrobenioidSystem.reindex_baseCategory

end FrobenioidSystem
end Iut
