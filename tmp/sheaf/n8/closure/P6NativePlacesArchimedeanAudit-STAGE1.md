# NativePlaces archimedean audit

- Task: Wave19.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6NativePlacesArchimedeanAudit.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0, no sorry.

## Decision

`NativePlaces X.S` is exactly the range of `V_mod_bijection`.  Hence:

`HasArchimedeanNativePlace X ↔ Nonempty (NumberField.InfinitePlace Fmod)`.

Declarations:
- `archimedeanNativePlace (w : InfinitePlace Fmod) : NativePlaces X.S`
  := `V_mod_bijection (NumberFieldPlace.infinite w)`;
- `archimedeanNativePlace_isInfinite`: its base comap is infinite;
- `hasArchimedeanNativePlace_of_infinitePlace`;
- `infinitePlace_of_hasArchimedeanNativePlace`;
- `nativePlaces_archimedean_iff`;
- `nativePlaces_all_finite_of_no_infinitePlace`.

## Applicability of Wave18

Wave18 `noAdm_of_archimedean_at` / `noP6Readout_of_archimedean_at` applies
whenever an infinite base place is supplied; the audit constructs the exact
native place from it.  If the base field has no infinite place, all native
places are finite and the Wave18 archimedean obstruction does not apply.

The Lean statement is conditional on `Nonempty (InfinitePlace Fmod)`; this
audit does not add a global complex-embedding instance for an arbitrary
number field, so it does not assert base-infinite-place existence
unconditionally.  No old L0.5 target, no arbitrary data.