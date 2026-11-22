import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteHodgeTheaterExample
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import tmp.sheaf.takkun.IutLean.HodgeTheater.Defs
import tmp.sheaf.takkun.IutLean.HodgeTheater.PrimeStripData
import tmp.sheaf.takkun.IutLean.LogTheta.LogShell
import tmp.sheaf.takkun.IutLean.LogTheta.Lattice
import tmp.sheaf.takkun.IutLean.LogTheta.Indeterminacy
import tmp.sheaf.xif.paper.Mzk1TakkunPrimeStripAdapterActual

/-!
# Thm 3.11 object bundle (reference): concrete Hodge theater / prime-strips /
# log-shell / lattice / tensor packets

Reuses only green modules: our `ConcreteHodgeTheaterExample`, `PrimeStripCore`
(via the adapter), `SourceLogShellCarrier`, `SourceProcessionCapsuleData`,
and Takkun `HodgeTheater/Defs`, `HodgeTheater/PrimeStripData`,
`LogTheta/LogShell`, `LogTheta/Lattice`, `LogTheta/Indeterminacy`.

These are the object-level inputs of IUT III Theorem 3.11; no mathematical
statement of 3.11 is asserted here (proof obligations stay separate).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311ObjectsActual

open LeanFormal.IUT

noncomputable section

universe uR uVQ uPlace uShell

/-- Concrete Hodge theater assembled from real lower-layer objects
(`gaussianHodgeTheater`). -/
def thm311Hodge (l : PrimeGeFive) : HodgeTheater l RationalPrimePlace :=
  gaussianHodgeTheater l

@[simp] theorem thm311Hodge_primeStrip (l : PrimeGeFive) :
    (thm311Hodge l).primeStrip = localFPrimeStrip :=
  rfl

/-- The Takkun `FhPrimeStrip` image of the concrete theater's prime-strip
(green adapter). -/
def thm311Fh (l : PrimeGeFive) :
    _root_.IUT.Frobenioid.FhPrimeStrip RationalPrimePlace :=
  LeanFormal.IUT.XiFPaper.Mzk1TakkunPrimeStripAdapterActual.takkunFhOfOur
    (thm311Hodge l).primeStrip

@[simp] theorem thm311Fh_G (l : PrimeGeFive) (v : RationalPrimePlace) :
    (thm311Fh l).G v = (thm311Hodge l).primeStrip.toDPrimeStrip.Pi v :=
  rfl

/-- Takkun log-theta lattice from a family of Theta-ellNF theaters. -/
def thm311Lattice (HT : Int × Int → _root_.IUT.HodgeTheater.Full) :
    _root_.IUT.LogTheta.LogThetaLattice where
  HT := HT

@[simp] theorem thm311Lattice_thetaColumn
    (HT : Int × Int → _root_.IUT.HodgeTheater.Full) (n m : Int) :
    (thm311Lattice HT).thetaColumn n m = HT (n, m) := rfl

@[simp] theorem thm311Lattice_logRow
    (HT : Int × Int → _root_.IUT.HodgeTheater.Full) (m n : Int) :
    (thm311Lattice HT).logRow m n = HT (n, m) := rfl

/-- Takkun log-shell whose carrier is our reduced source log-coordinate field
(IUT III Def 1.1(i) reduced core). -/
def thm311LogShell (D : SourceLogShellDatum.{uR}) :
    _root_.IUT.LogTheta.LogShell.{uR} where
  carrier := D.K
  addCommGroup := inferInstance

@[simp] theorem thm311LogShell_carrier (D : SourceLogShellDatum.{uR}) :
    (thm311LogShell D).carrier = D.K := rfl

/-- Tensor packets are provided by the green `SourceProcessionCapsuleData` module -/

/-- The finite theta packet (q^{j^2} values) of the concrete theater: the
Theta-pilot side's value data. -/
def thm311ThetaPacket (l : PrimeGeFive) : FiniteThetaPacket l :=
  (thm311Hodge l).thetaPacket

@[simp] theorem thm311ThetaPacket_q (l : PrimeGeFive) :
    (thm311ThetaPacket l).q = (1 / 2 : Real) := rfl

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311ObjectsActual
