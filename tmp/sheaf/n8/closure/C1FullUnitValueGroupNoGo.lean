import tmp.sheaf.n8.closure.C1PlaceValueGroupActual
import tmp.sheaf.n8.closure.C1FiberMonEquivAttempt
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# C1FullUnitValueGroupNoGo

Actual finite/infinite unit monoids contain an order-two element `-1`; the
value groups `Multiplicative ℤ` and `Multiplicative ℝ` are torsion-free.
Therefore no `MulEquiv` from the actual unit monoid to the value group exists.
This gives the exact no-go for the full-unit `C1FiberMonEquivData` target
(the quotient-by-kernel version is the one that is actually true).
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1FullUnitValueGroupNoGo

universe u v

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.N8Closure.C1FiberMonEquivAttempt
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F]

/-- No order-two element in `Multiplicative ℤ`. -/
lemma finiteValueGroup_sq_eq_one {h : finitePlaceValueGroup} (hh : h ^ 2 = 1) : h = 1 := by
  have hh' := congrArg Multiplicative.toAdd hh
  rw [pow_two] at hh'
  change Multiplicative.toAdd h + Multiplicative.toAdd h = 0 at hh'
  have hzero : Multiplicative.toAdd h = 0 := by omega
  exact Multiplicative.toAdd.injective hzero

/-- No order-two element in `Multiplicative ℝ`. -/
lemma archValueGroup_sq_eq_one {h : archimedeanValueGroup} (hh : h ^ 2 = 1) : h = 1 := by
  have hh' := congrArg Multiplicative.toAdd hh
  rw [pow_two] at hh'
  change Multiplicative.toAdd h + Multiplicative.toAdd h = 0 at hh'
  have hzero : Multiplicative.toAdd h = 0 := by linarith
  exact Multiplicative.toAdd.injective hzero

/-- General no-go: an order-two element on one side contradicts torsion-freeness
on the other. -/
lemma no_mulEquiv_of_order_two {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (g : G) (hg : g ≠ 1) (h2 : g ^ 2 = 1)
    (hH : ∀ h : H, h ^ 2 = 1 → h = 1) : False := by
  have h1 : e g = 1 := hH (e g) (by rw [← map_pow, h2, map_one])
  exact hg (e.injective (by simpa using h1))

/-- `-1 ≠ 1` in the finite completion units. -/
lemma finiteUnits_neg_one_ne_one (v : HeightOneSpectrum (𝓞 F)) :
    (-1 : (v.adicCompletion F)ˣ) ≠ 1 := by
  intro h
  have hv : (-1 : v.adicCompletion F) = 1 := congrArg Units.val h
  exact (by norm_num : (-1 : v.adicCompletion F) ≠ 1) hv

/-- `-1 ≠ 1` in the infinite completion units, by transport to ℝ or ℂ. -/
lemma infiniteUnits_neg_one_ne_one (w : NumberField.InfinitePlace F) :
    (-1 : (w.Completion)ˣ) ≠ 1 := by
  intro h
  have hv : (-1 : w.Completion) = 1 := congrArg Units.val h
  rcases w.isReal_or_isComplex with hreal | hcomplex
  · have := congrArg (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal) hv
    norm_num at this
  · have := congrArg (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex) hv
    norm_num at this

/-- No equivalence finite units -> finite value group. -/
theorem finiteUnit_not_mulEquiv_valueGroup
    (v : HeightOneSpectrum (𝓞 F)) :
    ¬ Nonempty ((v.adicCompletion F)ˣ ≃* finitePlaceValueGroup) := by
  rintro ⟨e⟩
  exact no_mulEquiv_of_order_two e (-1) (finiteUnits_neg_one_ne_one (F := F) v)
    (by simp) (fun h hh => finiteValueGroup_sq_eq_one hh)

/-- No equivalence infinite units -> infinite value group. -/
theorem infiniteUnit_not_mulEquiv_valueGroup
    (w : NumberField.InfinitePlace F) :
    ¬ Nonempty ((w.Completion)ˣ ≃* archimedeanValueGroup) := by
  rintro ⟨e⟩
  exact no_mulEquiv_of_order_two e (-1) (infiniteUnits_neg_one_ne_one (F := F) w)
    (by simp) (fun h hh => archValueGroup_sq_eq_one hh)

/-- No equivalence at either finite or infinite place. -/
theorem placeUnitMonoid_not_mulEquiv_valueGroup
    (P : NumberFieldPlaceIndex (F := F)) :
    ¬ Nonempty (PlaceUnitMonoid (F := F) P ≃* SourcePlaceValueGroup (F := F) P) := by
  cases P with
  | inl v => exact finiteUnit_not_mulEquiv_valueGroup (F := F) v
  | inr w => exact infiniteUnit_not_mulEquiv_valueGroup (F := F) w

/-- Exact no-go for the full-unit C1 target, conditional on the old strip
fiber being the actual unit monoid at the place. -/
theorem no_c1FiberMonEquivData_of_monEquivPlaceUnit
    {l : PrimeGeFive} {V : Type v} [Preorder V]
    (I : OriginalInput l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (v : V)
    (hmon : Nonempty ((I.primeStripAt 0 0).Mon v ≃*
      PlaceUnitMonoid (F := I.initial.arithmetic.Fmod) (e v))) :
    ¬ C1FiberMonEquivDataExists I e := by
  rintro ⟨D⟩
  rcases hmon with ⟨em⟩
  have ecomp : Nonempty (PlaceUnitMonoid (F := I.initial.arithmetic.Fmod) (e v) ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v)) :=
    ⟨em.symm.trans (D.fiberMonEquiv 0 0 v)⟩
  exact placeUnitMonoid_not_mulEquiv_valueGroup (F := I.initial.arithmetic.Fmod) (e v) ecomp

end LeanFormal.IUT.N8Closure.C1FullUnitValueGroupNoGo