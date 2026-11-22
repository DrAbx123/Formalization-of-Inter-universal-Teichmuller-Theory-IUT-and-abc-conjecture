/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataLabelActionReindexConsumer
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataLabelActionReindexGluingConsumer
import Iut.Foundations.SourceFrobenioidSystemPolyAction

/-!
# Consumer: system data of the label-reindexed pair-fields system

Re-packages the reindexed system together with its identity gluing and trivial
label action.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedData
    (fields : PairFields) (G : Type) [Group G] (g : G) :
    PairFieldsSystemData G where
  system := toSystemDataReindexed fields G g
  gluing := toSystemDataReindexedGluing fields G g
  labelAction := FrobenioidSystemPolyAction.trivial _ G

end PairFields

#check PairFields.toSystemDataReindexedData

end FrobenioidSystem
end Iut

-- revived for blocked-tail sweep

-- revive final tail
