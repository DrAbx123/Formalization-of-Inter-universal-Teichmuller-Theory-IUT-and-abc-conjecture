/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataLabelActionReindexedSystemDataConsumer

/-!
# Consumer: actual system of the reindexed pair system data

Extracts the actual `FrobenioidSystem` carried by the reindexed pair system
data, together with its base categories and axiom packages.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedDataSystem
    (fields : PairFields) (G : Type) [Group G] (g : G) :
    FrobenioidSystem Bool :=
  (toSystemDataReindexedData fields G g).system

@[simp] theorem toSystemDataReindexedDataSystem_presentation
    (fields : PairFields) (G : Type) [Group G] (g : G) (index : Bool) :
    (toSystemDataReindexedDataSystem fields G g).presentation index =
      (toSystemDataReindexedData fields G g).system.presentation index :=
  rfl

theorem toSystemDataReindexedDataSystem_baseCategory_isConnected
    (fields : PairFields) (G : Type) [Group G] (g : G) (index : Bool) :
    CategoryTheory.IsConnected
      ((toSystemDataReindexedDataSystem fields G g).baseCategory index) :=
  (toSystemDataReindexedData fields G g).system.baseCategory_isConnected index

noncomputable def toSystemDataReindexedDataSystem_axioms
    (fields : PairFields) (G : Type) [Group G] (g : G) (index : Bool) :
    ((toSystemDataReindexedDataSystem fields G g).presentation index)
      |>.preFrobenioid.FrobenioidAxioms :=
  ((toSystemDataReindexedData fields G g).system.presentation index).axioms

end PairFields

#check PairFields.toSystemDataReindexedDataSystem
#check PairFields.toSystemDataReindexedDataSystem_baseCategory_isConnected
#check PairFields.toSystemDataReindexedDataSystem_axioms

end FrobenioidSystem
end Iut
