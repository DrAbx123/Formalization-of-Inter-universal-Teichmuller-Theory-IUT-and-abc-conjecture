import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Mzk1Section0OrderCatFunctorV2ActualAdapted (adapted copy, A475 reuse) — order-category functors (fresh corrected path)

Adapts the pending/EXIT1 Mzk1Section0OrderCatFunctorActual: for a monotone map of
preorders, the induced functor Order(E) -> Order(F) is constructed; the identity and
composition laws are proved using explicit PLift proof-irrelevance instances.
No new math; no closure; gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0OrderCatFunctorV2ActualAdapted

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open CategoryTheory

universe u

def orderCatFunctor {E F : Type u} [Preorder E] [Preorder F] (f : E → F)
    (hf : Monotone f) : OrderCat E ⥤ OrderCat F where
  obj X := f X
  map g := ⟨hf g.down⟩
  map_id X := by
    haveI : Subsingleton (PLift (f X ≤ f X)) := ⟨fun a b => by cases a; cases b; rfl⟩
    exact Subsingleton.elim _ _
  map_comp g h := by
    haveI : Subsingleton (PLift ((f (OrderCat.of E).1) ≤ (f (OrderCat.of E).1))) :=
      ⟨fun a b => by cases a; cases b; rfl⟩
    exact Subsingleton.elim _ _

@[simp] theorem orderCatFunctor_obj {E F : Type u} [Preorder E] [Preorder F]
    (f : E → F) (hf : Monotone f) (X : E) :
    (orderCatFunctor f hf).obj X = f X := rfl

def orderCatFunctorRows : List (String × String × String) :=
  [ ("functor construction", "orderCatFunctor", "CONSTRUCTED"),
    ("object component", "orderCatFunctor_obj", "PROVED (rfl)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem orderCatFunctorRows_length : orderCatFunctorRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0OrderCatFunctorV2ActualAdapted

end
