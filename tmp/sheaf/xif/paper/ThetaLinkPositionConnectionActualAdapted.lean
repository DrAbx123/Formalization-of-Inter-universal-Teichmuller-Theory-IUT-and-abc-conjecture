import tmp.sheaf.xif.paper.LogThetaLatticeActual
import tmp.sheaf.xif.paper.ThetaLinkKummerObjectsActualAdapted

/-!
# Actual Theta-link position and lattice connection

The actual log-theta-lattice has nodes I.theaterAt n m and horizontal links
I.linkAt n m (n+1) m.  This file constructs the actual Theta-link comparison
object at a lattice position, including:

* the Hodge-theater link itself;
* its underlying FPrimeStrip equivalence;
* the exact equality with the lattice horizontal arrow;
* the exact equality with the actual position link at (0,0).

All equalities are actual rfl/transitivity facts; no hypothetical comparison
object is asserted and no inequality is judged.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ThetaLinkPositionConnectionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.LogThetaLatticeActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-- An actual Theta-link comparison at a lattice position. -/
structure ActualThetaLinkComparison
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  n : Int
  m : Int
  /-- the actual Hodge-theater link of the Theta-link -/
  link : HodgeTheaterLink
    ((ActualLogThetaLattice.actual (I := I)).node (n, m))
    ((ActualLogThetaLattice.actual (I := I)).node (n + 1, m))
  /-- its actual underlying F-prime-strip equivalence -/
  stripIso : FPrimeStripEquiv
    ((ActualLogThetaLattice.actual (I := I)).node (n, m)).primeStrip
    ((ActualLogThetaLattice.actual (I := I)).node (n + 1, m)).primeStrip
  /-- the strip equivalence is the projection of the Hodge-theater link -/
  stripIso_eq : stripIso = link.primeStripEquiv
  /-- the link is the actual lattice horizontal arrow -/
  link_eq_lattice :
    link = (ActualLogThetaLattice.actual (I := I)).horizontal n m

namespace ActualThetaLinkComparison

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual comparison object at (n,m), constructed from I.linkAt. -/
noncomputable def at (n m : Int) : ActualThetaLinkComparison (I := I) where
  n := n
  m := m
  link := I.linkAt n m (n + 1) m
  stripIso := (I.linkAt n m (n + 1) m).primeStripEquiv
  stripIso_eq := rfl
  link_eq_lattice := rfl

/-- The link of the actual comparison is the source I.linkAt. -/
@[simp] theorem at_link (n m : Int) :
    (at (I := I) n m).link = I.linkAt n m (n + 1) m := rfl

/-- The strip equivalence of the actual comparison is the source projection. -/
@[simp] theorem at_stripIso (n m : Int) :
    (at (I := I) n m).stripIso =
      (I.linkAt n m (n + 1) m).primeStripEquiv := rfl

/-- The actual comparison is the lattice horizontal arrow. -/
theorem at_link_eq_lattice (n m : Int) :
    (at (I := I) n m).link =
      (ActualLogThetaLattice.actual (I := I)).horizontal n m := rfl

/-- The actual comparison strip equivalence is the projection of the lattice
horizontal arrow. -/
theorem at_stripIso_eq_lattice (n m : Int) :
    (at (I := I) n m).stripIso =
      ((ActualLogThetaLattice.actual (I := I)).horizontal n m).primeStripEquiv := rfl

end ActualThetaLinkComparison

/-- The actual Theta-link at (0,0) connected to the actual lattice position. -/
noncomputable def actualThetaLinkComparison
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    ActualThetaLinkComparison (I := I) :=
  ActualThetaLinkComparison.at (I := I) 0 0

/-- The actual comparison at (0,0) has the actual position link. -/
theorem actualThetaLinkComparison_link_eq_position
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (actualThetaLinkComparison (I := I)).link =
      (actualThetaLinkPosition (I := I)).link := rfl

/-- The actual comparison at (0,0) is the lattice horizontal arrow at (0,0). -/
theorem actualThetaLinkComparison_link_eq_lattice
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (actualThetaLinkComparison (I := I)).link =
      (ActualLogThetaLattice.actual (I := I)).horizontal 0 0 := rfl

/-- The actual comparison at (0,0) is the source link I.linkAt 0 0 1 0. -/
theorem actualThetaLinkComparison_link_eq_linkAt
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (actualThetaLinkComparison (I := I)).link = I.linkAt 0 0 1 0 := rfl

/-- The actual strip equivalence of the (0,0) comparison is the projection of
I.linkAt 0 0 1 0. -/
theorem actualThetaLinkComparison_stripIso_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (actualThetaLinkComparison (I := I)).stripIso =
      (I.linkAt 0 0 1 0).primeStripEquiv := rfl

/-- The actual comparison and position agree in (n,m). -/
theorem actualThetaLinkComparison_position_n
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (actualThetaLinkComparison (I := I)).n = (actualThetaLinkPosition (I := I)).n := rfl

theorem actualThetaLinkComparison_position_m
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (actualThetaLinkComparison (I := I)).m = (actualThetaLinkPosition (I := I)).m := rfl

end LeanFormal.IUT.XiFPaper.ThetaLinkPositionConnectionActualAdapted

end
