/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsLabelActionConsumer
import Iut.Foundations.SourceFrobenioidSystemPolyActionReindex

/-!
# Consumer: reindexing the pair-fields system by label action

Reindexes the actual system assembled from `PairFields` by a label-group
element.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toFrobenioidSystemReindexed
    (fields : PairFields) (G : Type) [Group G] (g : G) :
    FrobenioidSystem Bool :=
  (toFrobenioidSystemPolyAction fields G).reindexSystem g

@[simp] theorem toFrobenioidSystemReindexed_presentation
    (fields : PairFields) (G : Type) [Group G] (g : G) (index : Bool) :
    (toFrobenioidSystemReindexed fields G g).presentation index =
      (PairFields.toFrobenioidSystem fields).presentation
        ((toFrobenioidSystemPolyAction fields G).labelAction g index) :=
  rfl

end PairFields

#check PairFields.toFrobenioidSystemReindexed
#check PairFields.toFrobenioidSystemReindexed_presentation

end FrobenioidSystem
end Iut
