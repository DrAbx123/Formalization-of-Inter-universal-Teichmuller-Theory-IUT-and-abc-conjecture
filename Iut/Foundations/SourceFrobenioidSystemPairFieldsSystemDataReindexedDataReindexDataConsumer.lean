/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataReindexedDataReindexGluingConsumer
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataConsumer
import Iut.Foundations.SourceFrobenioidSystemPolyAction

/-!
# Consumer: system data after iterated label reindexing

Re-packages the iterated-reindexed system with identity gluing and trivial
label action.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedDataReindexData
    (fields : PairFields) (G : Type) [Group G] (g h : G) :
    PairFieldsSystemData G where
  system := toSystemDataReindexedDataReindex fields G g h
  gluing := toSystemDataReindexedDataReindexGluing fields G g h
  labelAction := FrobenioidSystemPolyAction.trivial _ G

end PairFields

#check PairFields.toSystemDataReindexedDataReindexData

end FrobenioidSystem
end Iut
