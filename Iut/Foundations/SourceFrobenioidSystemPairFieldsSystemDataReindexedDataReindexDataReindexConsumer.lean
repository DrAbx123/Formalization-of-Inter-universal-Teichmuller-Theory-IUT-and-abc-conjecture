/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataReindexedDataReindexDataConsumer
import Iut.Foundations.SourceFrobenioidSystemPolyActionReindex

/-!
# Consumer: further label reindexing of the iterated system data

Reindexes the iterated-reindexed system data by another label-group element.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedDataReindexDataReindex
    (fields : PairFields) (G : Type) [Group G] (g h k : G) :
    FrobenioidSystem Bool :=
  (toSystemDataReindexedDataReindexData fields G g h).labelAction.reindexSystem k

end PairFields

#check PairFields.toSystemDataReindexedDataReindexDataReindex

end FrobenioidSystem
end Iut
