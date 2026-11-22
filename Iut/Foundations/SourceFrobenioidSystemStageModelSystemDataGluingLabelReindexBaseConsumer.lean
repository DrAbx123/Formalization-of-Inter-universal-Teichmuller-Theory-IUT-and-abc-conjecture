/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingLabelReindexConsumer

/-!
# Consumer: base categories of the label-reindexed system

The base category at a reindexed index is the original base category at the
label-action image index.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

variable (data : StageModelSystemDataGluing (K := K) Label G)

@[simp] theorem reindexedSystem_baseCategory
    (g : G) (index : NumberField.FinitePlace K × Label) :
    (data.reindexedSystem g).baseCategory index =
      data.system.base (data.applyLabel g index) :=
  rfl

theorem reindexedSystem_baseCategory_isConnected
    (g : G) (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      ((data.reindexedSystem g).baseCategory index) :=
  data.system.base_connected (data.applyLabel g index)

noncomputable def reindexedSystem_axioms
    (g : G) (index : NumberField.FinitePlace K × Label) :
    ((data.reindexedSystem g).presentation index).preFrobenioid.FrobenioidAxioms :=
  (data.system.presentation (data.applyLabel g index)).axioms

@[simp] theorem reindexedSystem_axioms_eq
    (g : G) (index : NumberField.FinitePlace K × Label) :
    data.reindexedSystem_axioms g index =
      (data.system.presentation (data.applyLabel g index)).axioms :=
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.reindexedSystem_baseCategory
#check StageModelSystemDataGluing.reindexedSystem_baseCategory_isConnected

end SourceFrobenioidSystem
end Iut
