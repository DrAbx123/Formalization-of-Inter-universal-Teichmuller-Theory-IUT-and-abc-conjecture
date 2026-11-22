/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # A531: pilot-side disambiguation ((0,0) Theta possible images vs (1,0) q-pilot) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PilotSideDisambiguationActual

/-- Lattice side of a pilot object in the log-theta-lattice: the Theta-pilot possible
images live at `(0,0)` and the q-pilot object at `(1,0)`; they are distinct objects and
must not be identified. -/
inductive PilotLatticeSide where
  | theta00
  | q10
deriving DecidableEq, Repr

/-- A pilot object tagged by its lattice side. -/
structure TaggedPilotObject (side : PilotLatticeSide) where
  label : String

/-- The two pilots are tagged differently: no identification. -/
theorem theta00_ne_q10 : PilotLatticeSide.theta00 ≠ PilotLatticeSide.q10 :=
  fun h => by cases h

/-- A comparison may only relate objects of the two sides through the LGP-link /
multiradial data; a definitional containment of one side in itself is excluded. -/
structure TwoSidedComparison where
  theta : TaggedPilotObject PilotLatticeSide.theta00
  q : TaggedPilotObject PilotLatticeSide.q10
  relation : Prop

end LeanFormal.IUT.XiFPaper.Mzk1PilotSideDisambiguationActual
