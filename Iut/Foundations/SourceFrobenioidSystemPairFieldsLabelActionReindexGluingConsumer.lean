/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsLabelActionReindexConsumer
import Iut.Foundations.SourceFrobenioidSystemGluing

/-!
# Consumer: gluing on the label-reindexed pair-fields system

Provides the identity gluing on the system obtained by reindexing `PairFields`
along a label-group element.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toFrobenioidSystemReindexedGluing
    (fields : PairFields) (G : Type) [Group G] (g : G) :
    FrobenioidSystemGluing
      (toFrobenioidSystemReindexed fields G g) :=
  FrobenioidSystemGluing.trivial _

end PairFields

#check PairFields.toFrobenioidSystemReindexedGluing

end FrobenioidSystem
end Iut

-- revived for blocked-tail sweep
