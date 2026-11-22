/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemConstant
import Iut.Foundations.SourceFrobenioidSystemPolyAction

/-!
# Label actions on constant systems

Any group action on the index type makes a constant system of Frobenioid
presentations into a poly-acting system.  This is the data-level form of a
label action on a constant subsystem (IUTchI, Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

noncomputable def constantPolyActionOf
    (presentation : FrobenioidPresentation.{u}) (iota : Type u)
    (G : Type u) [Group G] (labelAction : G →* Equiv.Perm iota) :
    FrobenioidSystemPolyAction (constant presentation iota) G where
  labelAction := labelAction

@[simp] theorem constantPolyActionOf_labelAction
    (presentation : FrobenioidPresentation.{u}) (iota : Type u)
    (G : Type u) [Group G] (labelAction : G →* Equiv.Perm iota) (g : G) :
    (constantPolyActionOf presentation iota G labelAction).labelAction g =
      labelAction g :=
  rfl

#check FrobenioidSystem.constantPolyActionOf

end FrobenioidSystem
end Iut
