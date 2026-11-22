import tmp.sheaf.takkun.IutLean.LogTheta.LogShell
import tmp.sheaf.takkun.IutLean.LogTheta.Lattice
import tmp.sheaf.xif.paper.O2ThetaObjectActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual

/-! Mainline (A503): O3 `MultiradialRepresentation` — a REAL object assembly of
  log-theta lattice + q/Theta pilots + hull.

Fields are all real objects (no Prop shells, no interface placeholders):
* Takkun `LogThetaLattice` / `LogChain` / `LogShell` (real structures);
* the q-pilot readout is our literal SHE double image `qPilotLogImage`
  (= Real.log ||q_V||, real local completion log);
* the Theta-pilot data is qpilot's O2 object `O2ThetaObject` (qroot/thetaValue/thetaLogVolume
  with the proved root relation `qroot^(2l) = q` and the independent readout
  `thetaLogVolume = globalThetaLogVolume`, no 1/(2l) rescaling);
* the hull is the hull lane's real `HullDetState` (positive packet + q + q_pos + log nonzero).

`multiradialRepresentationOf` constructs the object from these real data; the `_constructed`
theorems record each field equality and one genuinely proved property (packetDet positivity).
No sorry/axiom; no conclusion/Cor 3.12 claim. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1MultiradialRepresentationActual

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.O2ThetaObjectActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- O3 multiradial representation object: lattice + log-link chain + log-shell + q/Theta
  pilots + hull.  Every field is a real object. -/
structure MultiradialRepresentation [Fintype (Bad (nativePlaceSelection T))] where
  /-- Takkun log-theta lattice (grid of Theta+-ellNF Hodge theaters). -/
  lattice : IUT.LogTheta.LogThetaLattice
  /-- Takkun log-link chain (vertical direction). -/
  logChain : IUT.LogTheta.LogChain.{0}
  /-- Takkun log-shell object (a) carrier. -/
  shell : IUT.LogTheta.LogShell.{0}
  /-- qpilot O2 Theta-pilot object (qroot, thetaValue, thetaLogVolume). -/
  qTheta : O2ThetaObject T
  /-- A bad place at which the q-pilot readout is taken. -/
  nativePlace : Bad (nativePlaceSelection T)
  /-- q-pilot readout: the literal signed local q-log. -/
  qPilotReadout : Real
  qPilotReadout_eq : qPilotReadout = qPilotLogImage T nativePlace
  /-- The procession-averaged global Theta-pilot log-volume (independent readout). -/
  thetaAverage : Real
  thetaAverage_eq : thetaAverage = globalThetaLogVolume_average T
  /-- Hull data: positive packet + q parameter. -/
  hullState : HullDetState (SignedLabel l.value)

/-- Construct the O3 object from real data parameters. -/
def multiradialRepresentationOf [Fintype (Bad (nativePlaceSelection T))]
    (lattice : IUT.LogTheta.LogThetaLattice)
    (logChain : IUT.LogTheta.LogChain.{0})
    (shell : IUT.LogTheta.LogShell.{0})
    (qTheta : O2ThetaObject T)
    (nativePlace : Bad (nativePlaceSelection T))
    (hullState : HullDetState (SignedLabel l.value)) :
    MultiradialRepresentation T where
  lattice := lattice
  logChain := logChain
  shell := shell
  qTheta := qTheta
  nativePlace := nativePlace
  qPilotReadout := qPilotLogImage T nativePlace
  qPilotReadout_eq := rfl
  thetaAverage := globalThetaLogVolume_average T
  thetaAverage_eq := rfl
  hullState := hullState

/-- **Constructed (q-pilot):** the q-pilot readout is the literal q-log at the chosen
  bad place, not a parameter. -/
theorem mrr_qPilotReadout_constructed [Fintype (Bad (nativePlaceSelection T))]
    (lattice : IUT.LogTheta.LogThetaLattice)
    (logChain : IUT.LogTheta.LogChain.{0})
    (shell : IUT.LogTheta.LogShell.{0})
    (qTheta : O2ThetaObject T)
    (nativePlace : Bad (nativePlaceSelection T))
    (hullState : HullDetState (SignedLabel l.value)) :
    (multiradialRepresentationOf T lattice logChain shell qTheta nativePlace hullState).qPilotReadout =
      qPilotLogImage T nativePlace := rfl

/-- **Constructed (Theta pilot):** the averaged Theta readout is the qpilot O2 global
  procession average. -/
theorem mrr_thetaAverage_constructed [Fintype (Bad (nativePlaceSelection T))]
    (lattice : IUT.LogTheta.LogThetaLattice)
    (logChain : IUT.LogTheta.LogChain.{0})
    (shell : IUT.LogTheta.LogShell.{0})
    (qTheta : O2ThetaObject T)
    (nativePlace : Bad (nativePlaceSelection T))
    (hullState : HullDetState (SignedLabel l.value)) :
    (multiradialRepresentationOf T lattice logChain shell qTheta nativePlace hullState).thetaAverage =
      globalThetaLogVolume_average T := rfl

/-- **Constructed (log-shell instance):** the shell carrier carries the Takkun
  `AddCommGroup` instance. -/
def mrr_shell_carrier_constructed [Fintype (Bad (nativePlaceSelection T))]
    (lattice : IUT.LogTheta.LogThetaLattice)
    (logChain : IUT.LogTheta.LogChain.{0})
    (shell : IUT.LogTheta.LogShell.{0})
    (qTheta : O2ThetaObject T)
    (nativePlace : Bad (nativePlaceSelection T))
    (hullState : HullDetState (SignedLabel l.value)) :
    AddCommGroup (multiradialRepresentationOf T lattice logChain shell qTheta nativePlace hullState).shell.carrier :=
  inferInstance

/-- **Constructed (Theta values):** each Theta value readout is a global Theta log-volume
  (field of the O2 object, re-exported). -/
theorem mrr_thetaLogVolume_constructed [Fintype (Bad (nativePlaceSelection T))]
    (lattice : IUT.LogTheta.LogThetaLattice)
    (logChain : IUT.LogTheta.LogChain.{0})
    (shell : IUT.LogTheta.LogShell.{0})
    (qTheta : O2ThetaObject T)
    (nativePlace : Bad (nativePlaceSelection T))
    (hullState : HullDetState (SignedLabel l.value))
    (j : SignedLabel l.value) :
    (multiradialRepresentationOf T lattice logChain shell qTheta nativePlace hullState).qTheta.thetaLogVolume j =
      globalThetaLogVolume T j := by
  exact (multiradialRepresentationOf T lattice logChain shell qTheta nativePlace hullState).qTheta.thetaLogVolume_eq j

/-- **Proved (hull positivity):** the hull packet's determinant is positive (real hull data
  property; `packetDet` is the product of the positive packet entries). -/
theorem mrr_hull_packetDet_pos [Fintype (Bad (nativePlaceSelection T))]
    (lattice : IUT.LogTheta.LogThetaLattice)
    (logChain : IUT.LogTheta.LogChain.{0})
    (shell : IUT.LogTheta.LogShell.{0})
    (qTheta : O2ThetaObject T)
    (nativePlace : Bad (nativePlaceSelection T))
    (hullState : HullDetState (SignedLabel l.value)) :
    0 < packetDet (multiradialRepresentationOf T lattice logChain shell qTheta nativePlace hullState).hullState.packet := by
  rw [packetDet_eq_prod]
  exact Finset.prod_pos (fun i _ =>
    (multiradialRepresentationOf T lattice logChain shell qTheta nativePlace hullState).hullState.packet.positive i)

end

end LeanFormal.IUT.XiFPaper.Mzk1MultiradialRepresentationActual