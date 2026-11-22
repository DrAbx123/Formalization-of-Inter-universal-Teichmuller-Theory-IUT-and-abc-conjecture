/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemConstant
import Iut.Foundations.SourceFrobenioidSystemGluing
import Iut.Foundations.SourceFrobenioidSystemPolyAction

/-!
# Trivial gluing and poly-action on a constant system

The constant system built from one Frobenioid presentation carries the
identity gluing and the trivial label action.  This is a concrete data-level
instance of the system/gluing structures of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

/-- Identity gluing on a constant system. -/
noncomputable def constantGluing (presentation : FrobenioidPresentation.{u}) (iota : Type u) :
    FrobenioidSystemGluing (constant presentation iota) :=
  FrobenioidSystemGluing.trivial _

/-- Trivial label action on a constant system. -/
noncomputable def constantPolyAction (presentation : FrobenioidPresentation.{u}) (iota : Type u)
    (G : Type u) [Group G] :
    FrobenioidSystemPolyAction (constant presentation iota) G :=
  FrobenioidSystemPolyAction.trivial _ G

#check constantGluing
#check constantPolyAction

end FrobenioidSystem
end Iut
