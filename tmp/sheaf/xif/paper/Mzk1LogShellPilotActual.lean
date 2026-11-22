import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import tmp.sheaf.takkun.IutLean.LogTheta.LogShell

/-!
# q-pilot / Theta-pilot value objects and log-shell carrier (reference)

Reuses green modules: our `FiniteThetaPacket` (theta values `q^{j^2}` at
signed labels), `SourceLogShellCarrier` (IUT III Def 1.1 reduced core) and
Takkun `LogTheta/LogShell`.

The q-pilot value is the packet's `q`; the Theta-pilot values are the packet's
`scale j = q^{j^2}`.  This keeps the paper's Gaussian-value semantics (no
`q/(2l)` replacement).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellPilotActual

open LeanFormal.IUT

noncomputable section

universe u

/-- q-pilot value carried by a finite theta packet. -/
def qPilotValue {l : PrimeGeFive} (P : FiniteThetaPacket l) : Real := P.q

theorem qPilotValue_pos {l : PrimeGeFive} (P : FiniteThetaPacket l) :
    0 < qPilotValue P := P.q_pos

/-- Theta-pilot value `q^{j^2}` at a signed label. -/
def thetaPilotValue {l : PrimeGeFive} (P : FiniteThetaPacket l)
    (j : SignedLabel l.value) : Real := P.scale j

theorem thetaPilotValue_eq_qpow {l : PrimeGeFive} (P : FiniteThetaPacket l)
    (j : SignedLabel l.value) :
    thetaPilotValue P j = realThetaValue P.q j.1 := P.scale_eq j

theorem thetaPilotValue_pos {l : PrimeGeFive} (P : FiniteThetaPacket l)
    (j : SignedLabel l.value) : 0 < thetaPilotValue P j := P.scale_pos j

theorem thetaPilotValue_neg {l : PrimeGeFive} (P : FiniteThetaPacket l)
    (j : SignedLabel l.value) :
    thetaPilotValue P (SignedLabel.neg j) = thetaPilotValue P j :=
  P.scale_neg j

theorem log_thetaPilotValue {l : PrimeGeFive} (P : FiniteThetaPacket l)
    (j : SignedLabel l.value) :
    Real.log (thetaPilotValue P j) =
      (gaussExponent j.1).toNat * Real.log P.q := P.log_scale j

/-- Takkun log-shell whose carrier is the log-coordinate field of our reduced
source log-shell datum (IUT III Def 1.1(i) core). -/
def pilotLogShell (D : SourceLogShellDatum.{u}) :
    _root_.IUT.LogTheta.LogShell.{u} where
  carrier := D.K
  addCommGroup := inferInstance

@[simp] theorem pilotLogShell_carrier (D : SourceLogShellDatum.{u}) :
    (pilotLogShell D).carrier = D.K := rfl

end

end LeanFormal.IUT.XiFPaper.Mzk1LogShellPilotActual
