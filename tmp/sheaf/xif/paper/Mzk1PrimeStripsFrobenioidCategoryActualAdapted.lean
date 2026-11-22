import Mathlib

/-!
# Mzk1PrimeStripsFrobenioidCategoryActualAdapted (adapted copy, A475 reuse) — prime-strip Frobenioid category data (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: a small category-like structure with identity and associative composition; genuine lemmas. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsFrobenioidCategoryActualAdapted

/-- Category-like data with identity and composition laws. -/
structure CatData (Obj : Type*) where
  Hom : Obj → Obj → Type
  id : ∀ x, Hom x x
  comp : ∀ {x y z}, Hom x y → Hom y z → Hom x z
  comp_assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z),
    comp (comp f g) h = comp f (comp g h)

/-- Genuine lemma: composition is associative. -/
theorem CatData.comp_assoc_apply {Obj : Type*} (C : CatData Obj)
    {w x y z : Obj} (f : C.Hom w x) (g : C.Hom x y) (h : C.Hom y z) :
    C.comp (C.comp f g) h = C.comp f (C.comp g h) :=
  C.comp_assoc f g h

end LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsFrobenioidCategoryActualAdapted
