/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemConsumer
import Iut.Foundations.SourceFrobenioidSystemPolyAction

/-!
# Consumer: label action on the system assembled from pair fields

Provides the trivial label poly-action on the actual `FrobenioidSystem Bool`
assembled from `PairFields`.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toFrobenioidSystemPolyAction
    (fields : PairFields) (G : Type) [Group G] :
    FrobenioidSystemPolyAction (PairFields.toFrobenioidSystem fields) G :=
  FrobenioidSystemPolyAction.trivial _ G

@[simp] theorem toFrobenioidSystemPolyAction_labelAction
    (fields : PairFields) (G : Type) [Group G] :
    (toFrobenioidSystemPolyAction fields G).labelAction =
      (1 : G →* Equiv.Perm Bool) :=
  rfl

end PairFields

#check PairFields.toFrobenioidSystemPolyAction
#check PairFields.toFrobenioidSystemPolyAction_labelAction

end FrobenioidSystem
end Iut
