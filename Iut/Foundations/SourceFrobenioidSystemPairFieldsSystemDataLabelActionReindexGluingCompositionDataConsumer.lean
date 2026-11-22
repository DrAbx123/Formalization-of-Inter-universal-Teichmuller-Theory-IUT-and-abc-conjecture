/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataLabelActionReindexGluingCompositionConsumer
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataConsumer
import Iut.Foundations.SourceFrobenioidSystemPolyAction

/-!
# Consumer: system data with composed reindexed gluing

Re-packages the reindexed system with its composed gluing and trivial label
action.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedGluingCompData
    (fields : PairFields) (G : Type) [Group G] (g : G) :
    PairFieldsSystemData G where
  system := toSystemDataReindexed fields G g
  gluing := toSystemDataReindexedGluingComp fields G g
  labelAction := FrobenioidSystemPolyAction.trivial _ G

end PairFields

#check PairFields.toSystemDataReindexedGluingCompData

end FrobenioidSystem
end Iut
