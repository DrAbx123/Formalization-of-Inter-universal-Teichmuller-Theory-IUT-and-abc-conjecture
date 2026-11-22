/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3DDictionaryAssemblyActual
import Mathlib.Tactic
/-! # AUDIT/GAP: C3D status consumer (all unproved) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3DStatusConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1C3DDictionaryAssemblyActual
structure StatusConsumer where
  field : String
  consumedStatus : String
def consumers : List StatusConsumer :=
  [⟨"p", "not proved"⟩, ⟨"place", "not proved"⟩, ⟨"q", "not proved"⟩,
   ⟨"tensorIndex", "no equivalence"⟩, ⟨"tensorPlaces", "no equivalence"⟩,
   ⟨"tensorTuple", "no equivalence"⟩]
theorem no_proved : consumers.all (fun c => c.consumedStatus == "proved") = false := rfl
def rows : List String := ["p", "place", "q", "tensorIndex", "tensorPlaces", "tensorTuple"]
theorem rows_length : rows.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3DStatusConsumerActual
end