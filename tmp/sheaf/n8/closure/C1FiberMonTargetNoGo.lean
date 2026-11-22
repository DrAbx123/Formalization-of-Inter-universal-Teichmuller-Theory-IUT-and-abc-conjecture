import tmp.sheaf.n8.closure.C1PlaceValueGroupActual
import tmp.sheaf.n8.closure.C1FiberMonEquivAttempt
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# C1 fiberMonEquiv target: finite/infinite unit no-go

C1FiberMonEquivData requires, at every n,m,v,

  (I.primeStripAt n m).Mon v ≃* SourcePlaceValueGroup F (e v).

If the canonical old-strip Mon at a place is the actual unit monoid
PlaceUnitMonoid (units of the local completion), the target is impossible:

- finite branch: units contain -1 of order 2; finitePlaceValueGroup =
  Multiplicative Z is torsion-free;
- infinite branch: units contain -1 of order 2; archimedeanValueGroup =
  Multiplicative R is torsion-free.

Hence no MulEquiv PlaceUnitMonoid -> SourcePlaceValueGroup exists at either
branch.  The correct target is the quotient by the integral-unit (finite) or
norm-one (infinite) kernel, for which C1PlaceValueGroupActual supplies
placeUnitQuotientEquivValueGroup.  No arbitrary iso is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1FiberMonTargetNoGo

universe ua uv upi umon ui u v

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

/-- No order-two element in finitePlaceValueGroup = Multiplicative Z. -/
lemma finiteValueGroup_sq_eq_one {h : finitePlaceValueGroup} (hh : h ^ 2 = 1) : h = 1 := by
  have hh' := congrArg Multiplicative.toAdd hh
  rw [pow_two] at hh'
  rw [toAdd_mul, toAdd_one] at hh'
  have hzero : Multiplicative.toAdd h = 0 := by omega
  exact Multiplicative.toAdd.injective hzero

/-- No order-two element in archimedeanValueGroup = Multiplicative R. -/
lemma archValueGroup_sq_eq_one {h : archimedeanValueGroup} (hh : h ^ 2 = 1) : h = 1 := by
  have hh' := congrArg Multiplicative.toAdd hh
  rw [pow_two] at hh'
  rw [toAdd_mul, toAdd_one] at hh'
  have hzero : Multiplicative.toAdd h = 0 := by linarith
  exact Multiplicative.toAdd.injective hzero

/-- Generic order-two obstruction. -/
lemma no_mulEquiv_of_order_two {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (g : G) (hg : g ≠ 1) (h2 : g ^ 2 = 1)
    (hH : ∀ h : H, h ^ 2 = 1 → h = 1) : False := by
  have h1 : e g = 1 := hH (e g) (by rw [← map_pow, h2, map_one])
  exact hg (e.injective (by simpa using h1))

lemma finiteUnits_neg_one_ne_one (v : HeightOneSpectrum (𝓞 F)) :
    (-1 : (v.adicCompletion F)ˣ) ≠ 1 := by
  intro h
  have hv : (-1 : v.adicCompletion F) = 1 := congrArg Units.val h
  exact (by norm_num : (-1 : v.adicCompletion F) ≠ 1) hv

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

/-- Exact target no-go: if at one place the old prime-strip Mon is the actual
unit monoid PlaceUnitMonoid, then C1FiberMonEquivData is impossible. -/
theorem no_c1FiberMonEquivData_of_monEquivPlaceUnit
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))
    (v : V)
    (hmon : Nonempty ((I.primeStripAt 0 0).Mon v ≃*
      PlaceUnitMonoid (F := I.initial.arithmetic.Fmod) (e v))) :
    ¬ C1FiberMonEquivDataExists I e := by
  rintro ⟨D⟩
  rcases hmon with ⟨em⟩
  have ecomp : Nonempty
      (PlaceUnitMonoid (F := I.initial.arithmetic.Fmod) (e v) ≃*
        SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v)) :=
    ⟨em.symm.trans (D.fiberMonEquiv 0 0 v)⟩
  exact placeUnitMonoid_not_mulEquiv_valueGroup
    (F := I.initial.arithmetic.Fmod) (e v) ecomp

/-- The quotient target is the actual donor: at every place the unit quotient
by the actual kernel is equivalent to the value group. -/
theorem placeUnitQuotient_target_actual
    (P : NumberFieldPlaceIndex (F := F)) :
    Nonempty ((PlaceUnitMonoid (F := F) P ⧸ placeUnitKernel (F := F) P) ≃*
      SourcePlaceValueGroup (F := F) P) :=
  ⟨placeUnitQuotientEquivValueGroup (F := F) P⟩

end LeanFormal.IUT.N8Closure.C1FiberMonTargetNoGo
