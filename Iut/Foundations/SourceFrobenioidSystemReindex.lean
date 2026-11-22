/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Reindexing a system of Frobenioids

Precomposition of the index type.  This is the formal operation used when a
label poly-action or a place/label family pulls a system of Frobenioids back
to another index set (cf. IUTchI, Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota iota' : Type u}

/-- Pull back a system along a map of index types. -/
def reindex (system : FrobenioidSystem iota) (map : iota' -> iota) :
    FrobenioidSystem iota' where
  presentation := fun index => system.presentation (map index)

@[simp] theorem reindex_presentation
    (system : FrobenioidSystem iota) (map : iota' -> iota) (index : iota') :
    (system.reindex map).presentation index = system.presentation (map index) :=
  rfl

@[simp] theorem reindex_id (system : FrobenioidSystem iota) :
    system.reindex id = system :=
  rfl

@[simp] theorem reindex_comp
    (system : FrobenioidSystem iota) {middle : Type u}
    (first : iota' -> middle) (second : middle -> iota) :
    (system.reindex second).reindex first =
      system.reindex (fun index => second (first index)) :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.reindex
#check FrobenioidSystem.reindex_id
#check FrobenioidSystem.reindex_comp

end Iut
