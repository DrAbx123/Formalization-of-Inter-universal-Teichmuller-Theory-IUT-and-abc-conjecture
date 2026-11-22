/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemBaseCategoryFamilyAxioms

/-!
# Label action on the place/label base-category family

The label component does not affect the base category, which depends only on
the finite place.  This records the base-category compatibility of the
place/label label action (IUTchI, Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

/-- Act by permuting the label component of a place/label index. -/
def stageBaseLabelAction (action : G →* Equiv.Perm Label)
    (g : G) (index : NumberField.FinitePlace K × Label) :
    NumberField.FinitePlace K × Label :=
  (index.1, action g index.2)

/-- The base category is invariant under the label action. -/
@[simp] theorem stageBaseCategoryFamily_labelAction
    (action : G →* Equiv.Perm Label) (g : G)
    (index : NumberField.FinitePlace K × Label) :
    stageBaseCategoryFamily (K := K) Label (stageBaseLabelAction action g index) =
      stageBaseCategoryFamily (K := K) Label index :=
  rfl

#check stageBaseLabelAction
#check stageBaseCategoryFamily_labelAction

end SourceFrobenioidSystem
end Iut
