/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemReindex
import Iut.Foundations.SourceFrobenioidSystemConstant

/-!
# Reindexing a constant system

Reindexing a constant family of Frobenioid presentations along any map of
index types gives the constant family on the new index type.  This is the
trivial compatibility used when a poly-action moves a constant subsystem.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota iota' : Type u}

theorem reindex_constant
    (presentation : FrobenioidPresentation.{u}) (map : iota' -> iota) :
    (constant presentation iota).reindex map =
      constant presentation iota' :=
  rfl

#check FrobenioidSystem.reindex_constant

end FrobenioidSystem
end Iut
