/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataConsumer
import Iut.Foundations.SourceFrobenioidSystemPolyActionReindex

/-!
# Consumer: label reindexing of the pair-fields system data

Reindexes the actual system carried by `PairFieldsSystemData` along its label
poly-action.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexed
    (fields : PairFields) (G : Type) [Group G] (g : G) :
    FrobenioidSystem Bool :=
  (toSystemData fields G).labelAction.reindexSystem g

@[simp] theorem toSystemDataReindexed_presentation
    (fields : PairFields) (G : Type) [Group G] (g : G) (index : Bool) :
    (toSystemDataReindexed fields G g).presentation index =
      (toSystemData fields G).system.presentation
        ((toSystemData fields G).labelAction.labelAction g index) :=
  rfl

end PairFields

#check PairFields.toSystemDataReindexed
#check PairFields.toSystemDataReindexed_presentation

end FrobenioidSystem
end Iut

-- revived for blocked-tail sweep
