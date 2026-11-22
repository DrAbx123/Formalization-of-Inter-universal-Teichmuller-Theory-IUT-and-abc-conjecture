/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataReindexedDataReindexConsumer
import Iut.Foundations.SourceFrobenioidSystemGluing

/-!
# Consumer: gluing on the iterated label-reindexed system data

Identity gluing on the system obtained by two successive label-action
reindexings.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedDataReindexGluing
    (fields : PairFields) (G : Type) [Group G] (g h : G) :
    FrobenioidSystemGluing
      (toSystemDataReindexedDataReindex fields G g h) :=
  FrobenioidSystemGluing.trivial _

end PairFields

#check PairFields.toSystemDataReindexedDataReindexGluing

end FrobenioidSystem
end Iut
