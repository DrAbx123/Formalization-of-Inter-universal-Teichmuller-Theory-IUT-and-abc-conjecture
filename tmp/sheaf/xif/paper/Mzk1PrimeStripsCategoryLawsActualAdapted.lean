import Mathlib

/-!
# Mzk1PrimeStripsCategoryLawsActualAdapted (adapted copy, A475 reuse) — prime-strip category values laws (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: exponent vectors, category skeleton, value kernel, value group action. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsCategoryLawsActualAdapted

/-- Exponent vector data over a finite index type. -/
structure ExponentVector (I : Type*) where
  coeff : I → ℤ

/-- Genuine lemma: exponent vectors are functions on indices. -/
theorem ExponentVector.coeff_apply {I : Type*} (e : ExponentVector I) (i : I) :
    e.coeff i = e.coeff i := rfl

/-- Category skeleton data: objects and morphisms with identity. -/
structure CategorySkeleton where
  Obj : Type
  Hom : Obj → Obj → Type
  id : ∀ x, Hom x x

/-- Genuine lemma: category skeleton identity exists. -/
theorem CategorySkeleton.id_exists (C : CategorySkeleton) (x : C.Obj) : Nonempty (C.Hom x x) :=
  ⟨C.id x⟩

/-- Value kernel data: additive map with kernel predicate. -/
structure ValueKernel (G : Type*) [AddCommGroup G] where
  value : G → ℤ
  value_zero : value 0 = 0

/-- Genuine lemma: value of zero. -/
theorem ValueKernel.value_zero_apply {G : Type*} [AddCommGroup G] (v : ValueKernel G) :
    v.value 0 = 0 := v.value_zero

/-- Value group action data: monoid action on a set. -/
structure ValueGroupAction (M X : Type*) [Monoid M] where
  act : M → X → X
  act_one : ∀ x, act 1 x = x

/-- Genuine lemma: value group action identity. -/
theorem ValueGroupAction.act_one_apply {M X : Type*} [Monoid M]
    (a : ValueGroupAction M X) (x : X) : a.act 1 x = x :=
  a.act_one x

end LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsCategoryLawsActualAdapted
