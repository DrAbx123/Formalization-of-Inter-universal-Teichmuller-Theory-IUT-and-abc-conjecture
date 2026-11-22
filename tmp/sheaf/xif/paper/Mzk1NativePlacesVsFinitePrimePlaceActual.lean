/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # GAP: NativePlaces vs FinitePrimePlace are different types -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1NativePlacesVsFinitePrimePlaceActual
structure TypeDiffRow where
  item : String
  native : String
  finite : String
def diffRows : List TypeDiffRow :=
  [ ⟨"underlying", "subtype of NumberFieldPlace K", "subtype of Nat"⟩,
    ⟨"membership", "v ∈ S.tuple.source.V", "p ∈ primeStrip 2 7"⟩,
    ⟨"cardinality source", "NativePlaces X.S", "FinitePrimePlace 2 7"⟩,
    ⟨"canonical map", "nativePlaceEquiv : NativePlaces ≃ NumberFieldPlaceIndex Fmod", "toRationalPrimePlace"⟩ ]
theorem diffRows_length : diffRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativePlacesVsFinitePrimePlaceActual
end