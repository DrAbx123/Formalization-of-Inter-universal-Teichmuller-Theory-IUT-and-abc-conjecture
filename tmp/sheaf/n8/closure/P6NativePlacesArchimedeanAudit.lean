import tmp.sheaf.n8.closure.UnitSphereReadoutDonorActual
import tmp.sheaf.n8.closure.NativeInput

/-!
# NativePlaces archimedean audit

Decides whether the native V-section places can contain an infinite place.
`NativePlaces X.S` is exactly the range of `V_mod_bijection`; hence it has an
infinite place iff the base field `X.S.arithmetic.Fmod` has an infinite place.

This determines the applicability of the Wave18 archimedean Adm/P6Readout
no-go: it applies exactly when the base field has an infinite place, and does
not apply if all native places are finite.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.UnitSphereReadoutDonorActual

namespace LeanFormal.IUT.N8Closure.P6NativePlacesArchimedeanAudit

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The native place corresponding to a base infinite place. -/
noncomputable def archimedeanNativePlace
    (w : NumberField.InfinitePlace X.S.arithmetic.Fmod) :
    NativePlaces X.S :=
  X.S.tuple.source.V_mod_bijection (NumberFieldPlace.infinite w)

/-- The constructed native place is infinite over the base. -/
theorem archimedeanNativePlace_isInfinite
    (w : NumberField.InfinitePlace X.S.arithmetic.Fmod) :
    NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod)
        (archimedeanNativePlace X w).1) := by
  have hsymm : X.S.tuple.source.V_mod_bijection.symm
      (archimedeanNativePlace X w) = NumberFieldPlace.infinite w := by
    unfold archimedeanNativePlace
    rw [Equiv.symm_apply_apply]
  have hcomap := X.S.tuple.source.V_place_comap (archimedeanNativePlace X w)
  rw [hcomap, hsymm]
  exact trivial

/-- A base infinite place gives an archimedean native place. -/
theorem hasArchimedeanNativePlace_of_infinitePlace
    (w : NumberField.InfinitePlace X.S.arithmetic.Fmod) :
    HasArchimedeanNativePlace (X := X) :=
  ⟨archimedeanNativePlace X w, archimedeanNativePlace_isInfinite X w⟩

/-- Conversely, an archimedean native place gives a base infinite place. -/
theorem infinitePlace_of_hasArchimedeanNativePlace
    (h : HasArchimedeanNativePlace (X := X)) :
    Nonempty (NumberField.InfinitePlace X.S.arithmetic.Fmod) := by
  obtain ⟨v, hv⟩ := h
  cases hP : (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1) with
  | finite p =>
      rw [hP] at hv
      exact False.elim hv
  | infinite w => exact ⟨w⟩

/-- Exact decision: NativePlaces has an infinite place iff the base field does. -/
theorem nativePlaces_archimedean_iff :
    HasArchimedeanNativePlace (X := X) ↔
      Nonempty (NumberField.InfinitePlace X.S.arithmetic.Fmod) :=
  ⟨infinitePlace_of_hasArchimedeanNativePlace (X := X),
    fun h => h.elim (fun w => hasArchimedeanNativePlace_of_infinitePlace X w)⟩

/-- If the base field has no infinite place, all native places are finite. -/
theorem nativePlaces_all_finite_of_no_infinitePlace
    (h : ¬ Nonempty (NumberField.InfinitePlace X.S.arithmetic.Fmod)) :
    ¬ HasArchimedeanNativePlace (X := X) := by
  intro hnat
  exact h ((nativePlaces_archimedean_iff X).mp hnat)

end LeanFormal.IUT.N8Closure.P6NativePlacesArchimedeanAudit