/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemGluing
import Iut.Foundations.SourceFrobenioidSystemReindex

/-!
# Reindexing gluing data

Pull back gluing data along a map of index types.  This is used when a label
action or a place/label family reindexes a glued system of Frobenioids
(IUTchI, Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystemGluing

variable {iota iota' : Type u} {system : FrobenioidSystem iota}
variable (gluing : FrobenioidSystemGluing system) (map : iota' -> iota)

/-- Reindex gluing data along a map of index types. -/
def reindex : FrobenioidSystemGluing (system.reindex map) where
  relation := fun source target => gluing.relation (map source) (map target)
  equivalence := fun {source target} related => gluing.equivalence related

end FrobenioidSystemGluing

#check FrobenioidSystemGluing.reindex

end Iut
