import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-!
# S3137: the log-shell-ready positions of the log-theta-lattice

IUT III, Remark 1.4.1, (ii) (pp. 46--47), and Remark 3.8.3 (p. 115): in order
to use the theory of log-shells -- and hence to construct the multiradial
representation of the Gaussian monoids -- the Theta±ellNF-Hodge theater in
which one operates must appear as the *codomain of a log-link*, i.e. of a
vertical arrow of the log-theta-lattice; every execution of a horizontal arrow
(Theta x mu LGP-link) obligates a subsequent vertical arrow.  At the level of
the lattice indices Z x Z this means:

* the log-shell-ready positions (n,m) are exactly those with m >= 1;
* at every log-shell-ready position the preceding full log-link is the actual
  source link from (n,m-1) to (n,m);
* the Theta-pilot position (0,0) (Definition 3.8, (i)) and the q-pilot
  position (1,0) are NOT log-shell-ready, while their common vertical
  successor (1,1) and the position (0,1) of the comparison square are.

The actual preceding log-link at each log-shell-ready position is the actual
source link I.linkAt (no new carrier, no fake link), and the actual theta-packet
q/scale invariance between a position and its predecessor is proved.  No
arbitrary data, no True/PUnit, no sorry, no axiom.  WRITE-ONLY.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137LogThetaLatticeLogShellReadyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-- The nodes of the log-theta-lattice. -/
abbrev LatticeIndex : Type := Int × Int

/-- A node is log-shell-ready when it is a codomain of a vertical (log) arrow,
i.e. when its vertical coordinate is at least 1 (Remark 1.4.1, (ii)). -/
def logShellReady (p : LatticeIndex) : Prop := 1 ≤ p.2

theorem logShellReady_iff (p : LatticeIndex) :
    logShellReady p ↔ 1 ≤ p.2 := Iff.rfl

/-- The predecessor of a node along its vertical line: the domain of the full
log-link ending at the node. -/
def verticalPredecessor (p : LatticeIndex) : LatticeIndex := (p.1, p.2 - 1)

/-- The predecessor reaches the node by the (0,1)-shift. -/
theorem verticalPredecessor_target (p : LatticeIndex) :
    verticalIndex (verticalPredecessor p) = p := by
  rcases p with ⟨n, m⟩
  simp [verticalPredecessor, verticalIndex]


/-- The actual full log-link ending at a node: the actual source link from the
vertical predecessor (Remark 1.4.1, (ii); Definition 3.8, (iii)). -/
def actualPrecedingLogLink (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (p : LatticeIndex) :
    HodgeTheaterLink (I.theaterAt (verticalPredecessor p).1
      (verticalPredecessor p).2) (I.theaterAt p.1 p.2) :=
  I.linkAt (verticalPredecessor p).1 (verticalPredecessor p).2 p.1 p.2

theorem actualPrecedingLogLink_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (p : LatticeIndex) :
    actualPrecedingLogLink I p = I.linkAt p.1 (p.2 - 1) p.1 p.2 := rfl

/-- The actual q-invariance of the preceding full log-link. -/
theorem precedingLogLink_q (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (p : LatticeIndex) :
    (I.theaterAt p.1 (p.2 - 1)).thetaPacket.q =
      (I.theaterAt p.1 p.2).thetaPacket.q :=
  I.linkAt_q p.1 (p.2 - 1) p.1 p.2

/-- The actual signed-scale invariance of the preceding full log-link. -/
theorem precedingLogLink_scale (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (p : LatticeIndex) (j : SignedLabel l.value) :
    (I.theaterAt p.1 (p.2 - 1)).thetaPacket.scale j =
      (I.theaterAt p.1 p.2).thetaPacket.scale j :=
  I.linkAt_scale p.1 (p.2 - 1) p.1 p.2 j

/-- The Theta-pilot position (0,0) (IUT III, Definition 3.8, (i)). -/
def thetaPilotPosition : LatticeIndex := (0, 0)

/-- The q-pilot position (1,0) (IUT III, Definition 3.8, (i)). -/
def qPilotPosition : LatticeIndex := (1, 0)

/-- The position (0,1) of the comparison square. -/
def logShellPosition : LatticeIndex := (0, 1)

/-- The position (1,1) of the comparison square. -/
def comparisonPosition : LatticeIndex := (1, 1)

theorem thetaPilot_not_logShellReady : ¬ logShellReady thetaPilotPosition := by
  simp only [logShellReady, thetaPilotPosition]
  decide

theorem qPilot_not_logShellReady : ¬ logShellReady qPilotPosition := by
  simp only [logShellReady, qPilotPosition]
  decide

theorem logShellPosition_logShellReady : logShellReady logShellPosition := by
  simp only [logShellReady, logShellPosition]
  decide

theorem comparisonPosition_logShellReady : logShellReady comparisonPosition := by
  simp only [logShellReady, comparisonPosition]
  decide

/-- The comparison square's positions (1,0) and (0,1) are the two (1,0)- and
(0,1)-shifts of the Theta-pilot position. -/
theorem qPilotPosition_shift : horizontalIndex thetaPilotPosition = qPilotPosition := rfl

theorem logShellPosition_shift : verticalIndex thetaPilotPosition = logShellPosition := rfl

/-- The common vertical successor (1,1) of the q-pilot position. -/
theorem comparisonPosition_shift : verticalIndex qPilotPosition = comparisonPosition := rfl

/-- The position (0,1) of the comparison square is reached from the Theta-pilot
position by the vertical (log) arrow, and the position (1,1) from the q-pilot
position: these are the log-shell-ready positions used by the
q-pilot/Theta-pilot comparison (Remark 1.4.1, (ii)). -/
theorem comparison_logShell_positions_are_vertical_targets :
    logShellPosition = verticalIndex thetaPilotPosition ∧
      comparisonPosition = verticalIndex qPilotPosition := by
  exact ⟨rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.S3137LogThetaLatticeLogShellReadyActual