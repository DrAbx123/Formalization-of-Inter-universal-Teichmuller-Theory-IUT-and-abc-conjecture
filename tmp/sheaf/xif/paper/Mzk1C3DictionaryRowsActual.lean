/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT/GAP: C3-vs-D dictionary row inventory -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3DictionaryRowsActual
structure DictRow where
  field : String
  c3 : String
  d : String
  status : String
def dictionaryRows : List DictRow :=
  [ ⟨"p", "C3.p", "S2717C3.p", "identity not proved"⟩,
    ⟨"place", "C3.place", "S2717C3.place", "place equality not proved"⟩,
    ⟨"q", "C3.q", "S2717C3.q", "q compatibility not proved"⟩,
    ⟨"tensorIndex", "C3.tensorIndex", "S2717C3.tensorIndex", "no index equivalence"⟩,
    ⟨"tensorPlaces", "C3.tensorPlaces", "S2717C3.tensorPlaces", "no place compatibility"⟩,
    ⟨"tensorTuple", "C3.tensorTuple", "S2717C3.tensorTuple", "no tuple compatibility"⟩ ]
theorem dictionaryRows_length : dictionaryRows.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3DictionaryRowsActual
end