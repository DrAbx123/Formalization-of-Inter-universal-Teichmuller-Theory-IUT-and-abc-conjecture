/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsGluingConsumer
import Iut.Foundations.SourceFrobenioidSystemPairFieldsLabelActionConsumer

/-!
# Consumer: system data assembled from pair fields

Packages the actual two-component system together with its gluing and label
poly-action.  This is the data-level consumer of IUTchI, Definition 6.13, (i),
for the two-component system.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

structure PairFieldsSystemData (G : Type) [Group G] where
  system : FrobenioidSystem Bool
  gluing : FrobenioidSystemGluing system
  labelAction : FrobenioidSystemPolyAction system G

noncomputable def toSystemData
    (fields : PairFields) (G : Type) [Group G] :
    PairFieldsSystemData G where
  system := PairFields.toFrobenioidSystem fields
  gluing := PairFields.toFrobenioidSystemGluing fields
  labelAction := PairFields.toFrobenioidSystemPolyAction fields G

end PairFields

#check PairFields.PairFieldsSystemData
#check PairFields.toSystemData

end FrobenioidSystem
end Iut
