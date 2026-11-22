/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataLabelActionReindexConsumer
import Iut.Foundations.SourceFrobenioidSystemGluing

/-!
# Consumer: gluing on the label-reindexed pair-fields system data

Provides the identity gluing on the system data reindexed by a label-group
element.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedGluing
    (fields : PairFields) (G : Type) [Group G] (g : G) :
    FrobenioidSystemGluing
      (toSystemDataReindexed fields G g) :=
  FrobenioidSystemGluing.trivial _

end PairFields

#check PairFields.toSystemDataReindexedGluing

end FrobenioidSystem
end Iut

-- revived for blocked-tail sweep
