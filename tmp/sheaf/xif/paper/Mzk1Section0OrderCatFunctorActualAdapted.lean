import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
# Mzk1Section0OrderCatFunctorActualAdapted (adapted copy, A475 reuse) — functors of the order categories Order(E)
(corpus Section 0, l.1271-1276)

STEP 0 prior-art: AbsTopIII05Section0ObjectsActual (OrderwiseConnected, CountablyOrdered,
OrderCat + Category instance) -> REUSE; this file constructs the functor Order(E) -> Order(F)
induced by a monotone map of preorders and proves its basic laws.

No axiom/sorry; registry frozen 14041.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0OrderCatFunctorActualAdapted

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open CategoryTheory

universe u

/-- Prop-indexed lifts are subsingletons (proof irrelevance). -/
instance PLift.instSubsingletonOfProp (P : Prop) : Subsingleton (PLift P) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- A monotone map of preorders induces a functor of the corresponding order categories. -/
def orderCatFunctor {E F : Type u} [Preorder E] [Preorder F] (f : E → F) (hf : Monotone f) :
    OrderCat E ⥤ OrderCat F where
  obj X := f X
  map g := ⟨hf g.down⟩
  map_id X := Subsingleton.elim _ _
  map_comp g h := Subsingleton.elim _ _

/-- Component computation: the functor acts on objects by the monotone map. -/
@[simp] theorem orderCatFunctor_obj {E F : Type u} [Preorder E] [Preorder F]
    (f : E → F) (hf : Monotone f) (X : E) :
    (orderCatFunctor f hf).obj X = f X := rfl

/-- The identity monotone map induces the identity functor (object component). -/
theorem orderCatFunctor_id_obj {E : Type u} [Preorder E] (X : E) :
    (orderCatFunctor (fun x : E => x) monotone_id).obj X = X := rfl

/-- A strictly monotone map is monotone, hence induces a functor (basic instance). -/
def orderCatFunctorOfStrictMono {E F : Type u} [PartialOrder E] [PartialOrder F] (f : E → F)
    (hf : StrictMono f) : OrderCat E ⥤ OrderCat F :=
  orderCatFunctor f hf.monotone

/-- Order-category functor rows: (item, construction, status). -/
def orderCatFunctorRows : List (String × String × String) :=
  [ ("functor Order(E) -> Order(F) from a monotone map", "orderCatFunctor f hf", "CONSTRUCTED"),
    ("object component", "orderCatFunctor_obj", "PROVED (rfl)"),
    ("identity object component", "orderCatFunctor_id_obj", "PROVED (rfl)"),
    ("strictly monotone map gives a functor", "orderCatFunctorOfStrictMono", "CONSTRUCTED"),
    ("order category equivalence / full paper Order(E) theory", "not claimed", "NAMED") ]

/-- The order-category functor row record has five rows. -/
theorem orderCatFunctorRows_length : orderCatFunctorRows.length = 5 := rfl

#check orderCatFunctor
#check orderCatFunctor_obj
#check orderCatFunctor_id_obj
#check orderCatFunctorOfStrictMono
#check orderCatFunctorRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Section0OrderCatFunctorActualAdapted
end
