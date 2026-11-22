import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore

/-!
# Actual log-theta-lattice from the source Hodge-theater family

IUT III, section 1, Figure I.1, defines the log-theta-lattice with

* nodes indexed by (n,m) in Z x Z;
* vertical arrows given by log-links;
* horizontal arrows given by the Theta/Theta-x-mu/LGP-links.

The actual source input I : OriginalInput l V supplies

  I.theaterAt n m : HodgeTheater l V
  I.linkAt n m n' m' : HodgeTheaterLink (I.theaterAt n m) (I.theaterAt n' m')

with actual family transitivity I.linkAt_trans.  This file constructs the
actual lattice diagram: nodes, horizontal/vertical Hodge-theater links, the
commutative square, and the actual Theta-link at the (0,0) position.

No unknown/arbitrary arrow is used; every field is an actual I.linkAt.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.LogThetaLatticeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-- The actual log-theta-lattice diagram associated to a source input. -/
structure ActualLogThetaLattice (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- the Hodge-theater vertex at (n,m) -/
  node : Int × Int → HodgeTheater.{ua, uv, upi, umon} l V
  /-- horizontal Theta/LGP-link at (n,m) -/
  horizontal : ∀ n m : Int,
    HodgeTheaterLink (node (n, m)) (node (n + 1, m))
  /-- vertical log-link at (n,m) -/
  vertical : ∀ n m : Int,
    HodgeTheaterLink (node (n, m)) (node (n, m + 1))
  /-- the actual square commutes -/
  square : ∀ n m : Int,
    HodgeTheaterLink.trans (horizontal n m) (vertical (n + 1) m) =
      HodgeTheaterLink.trans (vertical n m) (horizontal n (m + 1))

namespace ActualLogThetaLattice

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual log-theta-lattice from I.theaterAt and I.linkAt. -/
noncomputable def actual : ActualLogThetaLattice (I := I) where
  node p := I.theaterAt p.1 p.2
  horizontal n m := I.linkAt n m (n + 1) m
  vertical n m := I.linkAt n m n (m + 1)
  square n m := by
    rw [I.linkAt_trans n m (n + 1) m (n + 1) (m + 1)]
    rw [I.linkAt_trans n m n (m + 1) (n + 1) (m + 1)]

/-- The node of the actual lattice is the source theater. -/
@[simp] theorem actual_node (n m : Int) :
    (ActualLogThetaLattice.actual I).node (n, m) = I.theaterAt n m := rfl

/-- The horizontal arrow is the actual source link. -/
@[simp] theorem actual_horizontal (n m : Int) :
    (ActualLogThetaLattice.actual I).horizontal n m = I.linkAt n m (n + 1) m := rfl

/-- The vertical arrow is the actual source link. -/
@[simp] theorem actual_vertical (n m : Int) :
    (ActualLogThetaLattice.actual I).vertical n m = I.linkAt n m n (m + 1) := rfl

/-- The actual horizontal q-invariance from the source link. -/
theorem actual_horizontal_q (n m : Int) :
    ((ActualLogThetaLattice.actual I).node (n, m)).thetaPacket.q =
      ((ActualLogThetaLattice.actual I).node (n + 1, m)).thetaPacket.q :=
  I.linkAt_q n m (n + 1) m

/-- The actual vertical q-invariance from the source link. -/
theorem actual_vertical_q (n m : Int) :
    ((ActualLogThetaLattice.actual I).node (n, m)).thetaPacket.q =
      ((ActualLogThetaLattice.actual I).node (n, m + 1)).thetaPacket.q :=
  I.linkAt_q n m n (m + 1)

/-- The actual horizontal signed-scale invariance from the source link. -/
theorem actual_horizontal_scale (n m : Int) (j : SignedLabel l.value) :
    ((ActualLogThetaLattice.actual I).node (n, m)).thetaPacket.scale j =
      ((ActualLogThetaLattice.actual I).node (n + 1, m)).thetaPacket.scale j :=
  I.linkAt_scale n m (n + 1) m j

/-- The actual vertical signed-scale invariance from the source link. -/
theorem actual_vertical_scale (n m : Int) (j : SignedLabel l.value) :
    ((ActualLogThetaLattice.actual I).node (n, m)).thetaPacket.scale j =
      ((ActualLogThetaLattice.actual I).node (n, m + 1)).thetaPacket.scale j :=
  I.linkAt_scale n m n (m + 1) j

end ActualLogThetaLattice

/-- An actual Theta-link position in the lattice. -/
structure ActualThetaLinkPosition (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  n : Int
  m : Int
  link : HodgeTheaterLink
    ((ActualLogThetaLattice.actual I).node (n, m))
    ((ActualLogThetaLattice.actual I).node (n + 1, m))
  link_eq : link = (ActualLogThetaLattice.actual I).horizontal n m

/-- The actual Theta-link at the (0,0) position. -/
noncomputable def actualThetaLinkPosition
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    ActualThetaLinkPosition (I := I) where
  n := 0
  m := 0
  link := I.linkAt 0 0 1 0
  link_eq := rfl

/-- The actual (0,0) Theta-link is the source link I.linkAt 0 0 1 0. -/
theorem actualThetaLinkPosition_link (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (actualThetaLinkPosition I).link = I.linkAt 0 0 1 0 := rfl

end LeanFormal.IUT.XiFPaper.LogThetaLatticeActual

end
