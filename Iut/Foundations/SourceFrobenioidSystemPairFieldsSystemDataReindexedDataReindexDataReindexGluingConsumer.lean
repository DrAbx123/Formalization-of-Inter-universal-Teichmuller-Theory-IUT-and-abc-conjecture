/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataReindexedDataReindexDataReindexConsumer
import Iut.Foundations.SourceFrobenioidSystemGluing

/-!
# Consumer: gluing on the thrice label-reindexed system data

Identity gluing on the system obtained by three successive label-action
reindexings.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedDataReindexDataReindexGluing
    (fields : PairFields) (G : Type) [Group G] (g h k : G) :
    FrobenioidSystemGluing
      (toSystemDataReindexedDataReindexDataReindex fields G g h k) :=
  FrobenioidSystemGluing.trivial _

end PairFields

#check PairFields.toSystemDataReindexedDataReindexDataReindexGluing

end FrobenioidSystem
end Iut
