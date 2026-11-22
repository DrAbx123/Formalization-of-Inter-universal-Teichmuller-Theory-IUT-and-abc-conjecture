/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Frobenioid: ramification-index transport data -/

namespace LeanFormal.IUT.XiFPaper.FrobenioidRamificationActual

/-- Recorded ramification index data (e(w) > 0 in the local extension law). -/
structure RamificationData where
  index : Nat
  pos : 0 < index

/-- The transported value coordinate: e(w) * delta. -/
def unitTransport (d : RamificationData) (delta : Int) : Int := (d.index : Int) * delta

theorem unitTransport_zero (d : RamificationData) : unitTransport d 0 = 0 := by
  unfold unitTransport
  ring

theorem unitTransport_add (d : RamificationData) (a b : Int) :
    unitTransport d (a + b) = unitTransport d a + unitTransport d b := by
  unfold unitTransport
  ring

theorem unitTransport_one (d : RamificationData) :
    unitTransport d 1 = (d.index : Int) := by
  unfold unitTransport
  ring

theorem unitTransport_pos (d : RamificationData) {delta : Int} (h : 0 < delta) :
    0 < unitTransport d delta := by
  unfold unitTransport
  exact Int.mul_pos (by exact_mod_cast d.pos) h

theorem index_pos (d : RamificationData) : 0 < d.index := d.pos

end LeanFormal.IUT.XiFPaper.FrobenioidRamificationActual
