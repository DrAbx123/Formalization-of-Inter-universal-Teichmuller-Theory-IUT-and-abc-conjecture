/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataLabelActionReindexedSystemDataConsumer
import Iut.Foundations.SourceFrobenioidSystemPolyActionReindex

/-!
# Consumer: iterated label reindexing of pair-fields system data

Reindexes the already-reindexed system data by another label-group element.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedDataReindex
    (fields : PairFields) (G : Type) [Group G] (g h : G) :
    FrobenioidSystem Bool :=
  (toSystemDataReindexedData fields G g).labelAction.reindexSystem h

end PairFields

#check PairFields.toSystemDataReindexedDataReindex

end FrobenioidSystem
end Iut
