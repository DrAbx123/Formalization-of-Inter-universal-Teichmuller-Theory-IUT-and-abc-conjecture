import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.NativeC1
import Mathlib

/-!
# C1 value group vs native local field: exact monoid no-go

C1 fiberMonEquiv targets

  SourcePlaceValueGroup F P = Multiplicative Z (finite) or Multiplicative R (infinite).

Both are multiplicative versions of an additive value group: their
multiplication is addition of integers/reals, and neither has an absorbing
element.

The native local field localFieldAt X w is a field.  Its zero is absorbing:
0 * z = 0 for every z.  A monoid isomorphism would transport an absorbing
element back to the source value group, contradicting no-absorbing.

Therefore no monoid isomorphism SourcePlaceValueGroup F P ≃* localFieldAt X w
exists.  This shows the monoid half of SourceNativeMonoidEquivTarget is not a
C1 donor.  No arbitrary iso is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1ValueGroupLocalFieldNoGo

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1

universe ua uv upi umon ui uK

/-- Multiplicative Z (additive value group Z) has no absorbing element. -/
theorem multiplicativeInt_no_absorbing :
    ¬ ∃ x : Multiplicative ℤ, ∀ y : Multiplicative ℤ, x * y = x := by
  rintro ⟨x, hx⟩
  have h := hx (Multiplicative.ofAdd (1 : ℤ))
  have h' : Multiplicative.toAdd x + 1 = Multiplicative.toAdd x := by
    simpa using congrArg Multiplicative.toAdd h
  omega

/-- Multiplicative R (additive value group R) has no absorbing element. -/
theorem multiplicativeReal_no_absorbing :
    ¬ ∃ x : Multiplicative ℝ, ∀ y : Multiplicative ℝ, x * y = x := by
  rintro ⟨x, hx⟩
  have h := hx (Multiplicative.ofAdd (1 : ℝ))
  have h' : Multiplicative.toAdd x + 1 = Multiplicative.toAdd x := by
    simpa using congrArg Multiplicative.toAdd h
  linarith

/-- SourcePlaceValueGroup has no absorbing element (both finite and infinite
branches). -/
theorem sourcePlaceValueGroup_no_absorbing
    (F : Type ua) [Field F] [NumberField F]
    (P : NumberFieldPlaceIndex (F := F)) :
    ¬ ∃ x : SourcePlaceValueGroup F P, ∀ y, x * y = x := by
  cases P with
  | inl _ =>
      simpa [SourcePlaceValueGroup, finitePlaceValueGroup] using
        multiplicativeInt_no_absorbing
  | inr _ =>
      simpa [SourcePlaceValueGroup, archimedeanValueGroup] using
        multiplicativeReal_no_absorbing

/-- A field's zero is absorbing. -/
theorem field_zero_absorbing (K : Type uK) [Field K] :
    ∀ z : K, (0 : K) * z = 0 :=
  fun z => zero_mul z

/-- Exact no-go: no monoid isomorphism from SourcePlaceValueGroup to any field. -/
theorem no_mulEquiv_sourcePlaceValueGroup_field
    (F : Type ua) [Field F] [NumberField F]
    (P : NumberFieldPlaceIndex (F := F))
    (K : Type uK) [Field K] :
    ¬ Nonempty (SourcePlaceValueGroup F P ≃* K) := by
  rintro ⟨e⟩
  let x : SourcePlaceValueGroup F P := e.symm 0
  have hx : ∀ y : SourcePlaceValueGroup F P, x * y = x := by
    intro y
    apply e.injective
    calc
      e (x * y) = e x * e y := map_mul e x y
      _ = 0 * e y := by rw [e.apply_symm_apply 0]
      _ = 0 := zero_mul (e y)
      _ = e x := (e.apply_symm_apply 0).symm
  exact sourcePlaceValueGroup_no_absorbing F P ⟨x, hx⟩

/-- Exact no-go for the actual native local field at a native place. -/
theorem no_mulEquiv_sourcePlaceValueGroup_localFieldAt
    {l : PrimeGeFive} (X : N8NativeInput l)
    (F : Type ua) [Field F] [NumberField F]
    (P : NumberFieldPlaceIndex (F := F))
    (w : NativePlaces X.S) [Field (localFieldAt X w)] :
    ¬ Nonempty (SourcePlaceValueGroup F P ≃* localFieldAt X w) :=
  no_mulEquiv_sourcePlaceValueGroup_field F P (localFieldAt X w)

end LeanFormal.IUT.N8Closure.C1ValueGroupLocalFieldNoGo
