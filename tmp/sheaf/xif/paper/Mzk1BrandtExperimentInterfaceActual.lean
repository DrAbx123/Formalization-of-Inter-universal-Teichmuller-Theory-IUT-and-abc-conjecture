/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A876/A878: path alpha (Brandt matrix experiment) - REJECTED / RETRACTED

USER DECISION (A878): the Brandt experiment (ROUTES 12.3(a)) is RETRACTED; the user
clarified that the intended three chains are ROUTES section 14, not section 10/12.

This file is kept only as a rejection record.  No data, no interface, and no claim is
maintained.  The experiment was never executed in this session; no numbers are fabricated.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1BrandtExperimentInterfaceActual

def brandtStatusRows : List (String × String) :=
  [ ("path alpha / Brandt experiment", "REJECTED / RETRACTED (A878)") ,
    ("experiment execution", "never executed; no data") ,
    ("replacement", "ROUTES section 14 chains (see coord/CHAIN2-CONTAINER-EXPERIMENT.md)") ]

theorem brandtStatusRows_length : brandtStatusRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1BrandtExperimentInterfaceActual
