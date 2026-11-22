/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1LanaIutIVLocalEstimateConsumerActual

/-! # A646 LANA IUT IV `LocalEstimate` consumer (Sha) — thin re-export

The actual external file `tmp/online/lana-agents__iut/iut-main/Iut/Concrete/LocalEstimate.lean`
constructs `TowerArithmetic.localEstimate : (D.invariants).LocalEstimate` from the
local-field theory of lana, but it cannot be imported here: lana pins
`lean v4.32.0 / mathlib@81a5d257c8` and depends on 10 external git packages not
vendored in this workspace.  Following A631/A646, this file is a thin, self-contained
re-export of the green LANA interface consumer
`Mzk1LanaIutIVLocalEstimateConsumerActual` (same `LocalEstimate` field shapes:
`height_estimate`, `volume_estimate`), used only as lana interface evidence.

No `sorry`, no `axiom`, no placeholder; not a gap closure (ABC gate NOT passed). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1LanaLocalEstimateConsumerShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1LanaIutIVLocalEstimateConsumerActual

/-- Re-export of the LANA local-estimate interface (consumer-level gap components). -/
abbrev LocalEstimate := Mzk1LanaIutIVLocalEstimateConsumerActual.LocalEstimate

/-- Re-export: the LANA local estimates assemble the ABC two-estimate package. -/
noncomputable def lanaLocalEstimate_toTwoEstimates
    {logVolume : Nat → Nat → Nat → Real} {hullVolume : Real}
    (L : LocalEstimate logVolume hullVolume) : ABCTwoEstimates :=
  Mzk1LanaIutIVLocalEstimateConsumerActual.LocalEstimate.toTwoEstimates L

/-- Re-export: the LANA local estimates imply `ABCConjecture` (conditional consumer). -/
theorem abc_of_localEstimate
    {logVolume : Nat → Nat → Nat → Real} {hullVolume : Real}
    (L : LocalEstimate logVolume hullVolume) : ABCConjecture :=
  Mzk1LanaIutIVLocalEstimateConsumerActual.abc_of_localEstimate L

def lanaConsumerRows : List (String × String × String) :=
  [ ("lana LocalEstimate fields", "height_estimate / volume_estimate", "GREEN interface (consumer re-export)"),
    ("lana TwoEstimates assembly", "LocalEstimate.toTwoEstimates", "PROVED"),
    ("lana conditional ABC consumer", "abc_of_localEstimate", "PROVED (conditional on estimates)"),
    ("external import", "Iut.Concrete.LocalEstimate (lana v4.32.0)", "IMPOSSIBLE offline (env mismatch)"),
    ("scope", "lana interface evidence only; NOT gap closure", "INTEGRITY") ]

theorem lanaConsumerRows_length : lanaConsumerRows.length = 5 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1LanaLocalEstimateConsumerShaActual.lanaLocalEstimate_toTwoEstimates
#print axioms LeanFormal.IUT.XiFPaper.Mzk1LanaLocalEstimateConsumerShaActual.abc_of_localEstimate

end LeanFormal.IUT.XiFPaper.Mzk1LanaLocalEstimateConsumerShaActual

end