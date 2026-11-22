import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import tmp.sheaf.takkun.IutLean.Frobenioid.PrimeStripSystem
import tmp.sheaf.xif.paper.Mzk1TakkunPrimeStripAdapterActual

/-! Mainline (A511-1): field-level adapter from our Hodge theater / prime-strip objects to
the Takkun `Frobenioid` structures.  Each mapping references an existing real declaration
(no new axioms, no shells):
* our `DPrimeStrip` has the same four fields as Takkun `Frobenioid.DPrimeStrip`;
* our `DPrimeStripEquiv` has the same three fields as Takkun's equiv;
* our `FPrimeStrip` maps via the existing `Mzk1TakkunPrimeStripAdapterActual.takkunFhOfOur`;
* our `HodgeTheater` maps through its `primeStrip` field; our `HodgeTheaterLink` maps via
  its `primeStripEquiv` field. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HodgeToTakkunFieldsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT

universe u v

/-- Our `DPrimeStrip` as a Takkun `Frobenioid.DPrimeStrip` (same fields). -/
def takkunDOfOur {V : Type*} (D : LeanFormal.IUT.DPrimeStrip V) :
    IUT.Frobenioid.DPrimeStrip.{0} V where
  Pi := D.Pi
  G := D.G
  proj := D.proj
  proj_surjective := D.proj_surjective

@[simp] theorem takkunDOfOur_Pi {V : Type*} (D : LeanFormal.IUT.DPrimeStrip V) (x : V) :
    (takkunDOfOur D).Pi x = D.Pi x := rfl

@[simp] theorem takkunDOfOur_G {V : Type*} (D : LeanFormal.IUT.DPrimeStrip V) (x : V) :
    (takkunDOfOur D).G x = D.G x := rfl

/-- Our `DPrimeStripEquiv` as a Takkun `DPrimeStripEquiv` (compat fields coincide). -/
def takkunDEquivOfOur {V : Type*} {D D' : LeanFormal.IUT.DPrimeStrip V}
    (φ : LeanFormal.IUT.DPrimeStripEquiv D D') :
    IUT.Frobenioid.DPrimeStripEquiv (takkunDOfOur D) (takkunDOfOur D') where
  isoPi := φ.isoPi
  isoG := φ.isoG
  compat := φ.compat

/-- Our `FPrimeStrip` translated to the Takkun `FhPrimeStrip` via the existing adapter. -/
def takkunFhOfOurFP {V : Type*} (F : LeanFormal.IUT.FPrimeStrip V) :
    IUT.Frobenioid.FhPrimeStrip.{0} V :=
  Mzk1TakkunPrimeStripAdapterActual.takkunFhOfOur F

/-- Our Hodge theater's prime-strip field as a Takkun `FhPrimeStrip`. -/
def takkunFhOfHodge {l : PrimeGeFive} {V : Type}
    (h : LeanFormal.IUT.HodgeTheater.{0, 0, 0, 0} l V) :
    IUT.Frobenioid.FhPrimeStrip.{0} V :=
  takkunFhOfOurFP h.primeStrip

/-- Our Hodge-theater link as a Takkun `FhPrimeStripEquiv` on the mapped prime strips. -/
def takkunFhEquivOfHodgeLink {l : PrimeGeFive} {V : Type}
    {s t : LeanFormal.IUT.HodgeTheater.{0, 0, 0, 0} l V}
    (L : LeanFormal.IUT.HodgeTheaterLink s t) :
    IUT.Frobenioid.FhPrimeStripEquiv (takkunFhOfHodge s) (takkunFhOfHodge t) :=
  Mzk1TakkunPrimeStripAdapterActual.takkunFhEquivOfOur L.primeStripEquiv

/-- The theta-packet `q` equality of a Hodge-theater link (re-exported from the real link
  field, not reproved). -/
theorem hodgeLink_theta_q_eq {l : PrimeGeFive} {V : Type}
    {s t : LeanFormal.IUT.HodgeTheater.{0, 0, 0, 0} l V}
    (L : LeanFormal.IUT.HodgeTheaterLink s t) :
    s.thetaPacket.q = t.thetaPacket.q :=
  L.theta_q_eq

/-- The theta-value scaling equality of a Hodge-theater link (re-exported). -/
theorem hodgeLink_theta_scale_eq {l : PrimeGeFive} {V : Type}
    {s t : LeanFormal.IUT.HodgeTheater.{0, 0, 0, 0} l V}
    (L : LeanFormal.IUT.HodgeTheaterLink s t) (j) :
    s.thetaPacket.scale j = t.thetaPacket.scale j :=
  L.theta_scale_eq j

end

end LeanFormal.IUT.XiFPaper.Mzk1HodgeToTakkunFieldsActual