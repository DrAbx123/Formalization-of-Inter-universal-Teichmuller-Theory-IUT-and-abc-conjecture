import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import tmp.sheaf.xif.paper.Mzk1TakkunPrimeStripAdapterActual
import tmp.sheaf.takkun.IutLean.HodgeTheater.Defs
import tmp.sheaf.takkun.IutLean.HodgeTheater.PrimeStripData
import tmp.sheaf.takkun.IutLean.LogTheta.Lattice

/-!
# O3 glue: Takkun Theta-ellNF `Full` theater and `PrimeStripSystem` -> O3 objects

Reuses green Takkun modules `HodgeTheater/Defs`, `HodgeTheater/PrimeStripData`,
`LogTheta/Lattice`, plus the green adapter `Mzk1TakkunPrimeStripAdapterActual`.
It provides projections from an existing `Full` theater (or a family of them) to
the O3 types (`PrimeStripSystem`, common `l`, Gaussian theta values, lattice),
and embeds our real `HodgeTheater` into the Takkun `FhPrimeStrip` image.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TakkunO3GlueActual

open LeanFormal.IUT

noncomputable section

universe u v

/-- The Takkun `PrimeStripSystem` carried by the additive half of a `Full` theater. -/
def o3PrimeStripSystemOfAdditive (A : _root_.IUT.HodgeTheater.AdditiveHodgeTheater) :
    _root_.IUT.HodgeTheater.PrimeStripSystem A.l :=
  A.primeStrips

/-- Common `l` of the additive and multiplicative halves (Takkun `Full.glue`). -/
theorem o3Full_add_mul_l (F : _root_.IUT.HodgeTheater.Full) :
    F.add.l = F.mul.l := F.glue

/-- Gaussian theta values carried by a `Full` theater (O3 theta data). -/
def o3ThetaValue (F : _root_.IUT.HodgeTheater.Full)
    (v : F.add.primeStrips.V) (j : Int) :=
  F.add.primeStrips.gaussian.thetaValueAt v j

/-- The Gaussian `sign` symmetry of the Takkun `PrimeStripSystem` transfers to
the O3 theta readout. -/
theorem o3ThetaValue_neg (F : _root_.IUT.HodgeTheater.Full)
    (v : F.add.primeStrips.V) (j : Int) :
    o3ThetaValue F v (-j) = o3ThetaValue F v j :=
  _root_.IUT.HodgeTheater.PrimeStripSystem.theta_symmetric F.add.primeStrips v j

/-- Our `HodgeTheater` (HodgeTheaterCore) maps into the Takkun `FhPrimeStrip`
image via the existing green adapter (`FPrimeStrip` -> Takkun `FhPrimeStrip`). -/
def o3FhOfOwn {l : PrimeGeFive} {V : Type u} (H : LeanFormal.IUT.HodgeTheater l V) :
    _root_.IUT.Frobenioid.FhPrimeStrip V :=
  LeanFormal.IUT.XiFPaper.Mzk1TakkunPrimeStripAdapterActual.takkunFhOfOur H.primeStrip

/-- Takkun log-theta lattice from a family of Theta-ellNF theaters (O2/O3 bridge). -/
def o3LatticeOfFullFamily (HT : Int × Int → _root_.IUT.HodgeTheater.Full) :
    _root_.IUT.LogTheta.LogThetaLattice where
  HT := HT

@[simp] theorem o3LatticeOfFullFamily_thetaColumn
    (HT : Int × Int → _root_.IUT.HodgeTheater.Full) (n m : Int) :
    (o3LatticeOfFullFamily HT).thetaColumn n m = HT (n, m) := rfl

@[simp] theorem o3LatticeOfFullFamily_logRow
    (HT : Int × Int → _root_.IUT.HodgeTheater.Full) (m n : Int) :
    (o3LatticeOfFullFamily HT).logRow m n = HT (n, m) := rfl

end

end LeanFormal.IUT.XiFPaper.Mzk1TakkunO3GlueActual
