/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataReindexedDataReindexDataReindexGluingConsumer
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataConsumer
import Iut.Foundations.SourceFrobenioidSystemPolyAction

/-!
# Consumer: system data after three label reindexings

Capstone data package: thrice-reindexed system + identity gluing + trivial
label action.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedDataReindexDataReindexData
    (fields : PairFields) (G : Type) [Group G] (g h k : G) :
    PairFieldsSystemData G where
  system := toSystemDataReindexedDataReindexDataReindex fields G g h k
  gluing := toSystemDataReindexedDataReindexDataReindexGluing fields G g h k
  labelAction := FrobenioidSystemPolyAction.trivial _ G

end PairFields

#check PairFields.toSystemDataReindexedDataReindexDataReindexData

end FrobenioidSystem
end Iut
