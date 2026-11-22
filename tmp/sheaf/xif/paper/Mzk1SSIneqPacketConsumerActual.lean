import Mathlib.Data.Real.Basic

/-!
# stepxi SSIneq packet consumer (A744/follow-up)

Consumer skeleton matching lana's
`Iut/WallEquiv/VcI.lean:741 logVol_hull_vcI_eq` and `:889 ssIneq_iff_packets`:

  logVol (hullOf (vcI)) = (∑ i, ∑ᶠ vQ, hullPacket i vQ) / nC;
  SSIneq D ↔ (sFactor(nC)-1)*absLogQ ≤ packetSum / nC.

The lana Wall olean is not built yet, so this file records the consumer interface
abstractly; it does not prove SSIneq. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqPacketConsumerActual

structure SSIneqPacketData where
  nC : Nat
  nC_pos : 0 < nC
  sFactor : Real
  absLogQ : Real
  logVolHull : Real
  packetSum : Real
  /-- lana `logVol_hull_vcI_eq`. -/
  hull_eq : logVolHull = packetSum / (nC : Real)
  ssIneq : Prop
  /-- lana `SSIneq` definitional shape. -/
  ssIneq_def : ssIneq ↔ (sFactor - 1) * absLogQ ≤ logVolHull

theorem logVol_hull_vcI_eq (D : SSIneqPacketData) :
    D.logVolHull = D.packetSum / (D.nC : Real) :=
  D.hull_eq

theorem ssIneq_iff_packets (D : SSIneqPacketData) :
    D.ssIneq ↔ (D.sFactor - 1) * D.absLogQ ≤ D.packetSum / (D.nC : Real) := by
  rw [D.ssIneq_def, D.hull_eq]

/-- A sufficient packet inequality closes SSIneq (converse direction only is recorded). -/
theorem ssIneq_of_packet_bound (D : SSIneqPacketData)
    (h : (D.sFactor - 1) * D.absLogQ ≤ D.packetSum / (D.nC : Real)) :
    D.ssIneq :=
  (ssIneq_iff_packets D).mpr h

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqPacketConsumerActual
