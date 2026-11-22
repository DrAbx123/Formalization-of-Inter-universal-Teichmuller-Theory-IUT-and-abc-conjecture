/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemConsumer
import Iut.Foundations.SourceFrobenioidSystemGluing

/-!
# Consumer: gluing data on the system assembled from pair fields

Provides the identity gluing on the actual `FrobenioidSystem Bool` assembled
from `PairFields`.  This is the minimal gluing consumer of IUTchI,
Definition 6.13, (i), for the two-component system.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toFrobenioidSystemGluing
    (fields : PairFields) :
    FrobenioidSystemGluing (PairFields.toFrobenioidSystem fields) :=
  FrobenioidSystemGluing.trivial _

@[simp] theorem toFrobenioidSystemGluing_relation
    (fields : PairFields) (source target : Bool) :
    (toFrobenioidSystemGluing fields).relation source target ↔
      source = target :=
  Iff.rfl

end PairFields

#check PairFields.toFrobenioidSystemGluing
#check PairFields.toFrobenioidSystemGluing_relation

end FrobenioidSystem
end Iut
