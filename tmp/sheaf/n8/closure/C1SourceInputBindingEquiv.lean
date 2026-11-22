import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.C1Actual

/-! # Exact equivalence between the C1 binding and its four actual data

`SourceInputBinding I` is a single place-data record whose fields are exactly
the four actual C1 data of `C1ActualData I`. This file proves the exact
Nonempty equivalence, so the remaining C1 existence gap is exactly the
existence of the four data, not a hidden theorem about the binding.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceInputBinding

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C1Actual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-- The C1 binding is inhabited exactly when its four actual data are. -/
theorem sourceInputBinding_nonempty_iff_c1ActualData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Nonempty (SourceInputBinding I) ↔ Nonempty (C1ActualData I) := by
  constructor
  · rintro ⟨S⟩
    let D : C1ActualData I :=
      { placeEquiv := S.place.placeEquiv
        selected := S.place.selected
        selected_realization := S.place.selected_realization
        fiberMonEquiv := S.place.fiberMonEquiv }
    exact ⟨D⟩
  · rintro ⟨D⟩
    exact ⟨sourceInputBindingOfActual I D⟩

end LeanFormal.IUT.N8Closure.SourceInputBinding

end