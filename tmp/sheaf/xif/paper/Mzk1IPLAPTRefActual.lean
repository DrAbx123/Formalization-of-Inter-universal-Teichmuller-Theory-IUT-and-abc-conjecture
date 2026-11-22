import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import tmp.sheaf.takkun.IutLean.HodgeTheater.Defs
import tmp.sheaf.takkun.IutLean.HodgeTheater.PrimeStripData

/-!
# IPL / APT / dsc object references (four-triangle 3.12 route)

Reuses green own `HodgeTheaterCore`/`PrimeStripCore` and green Takkun
`HodgeTheater/Defs`/`PrimeStripData`:
* **IPL** shape: equivalences of F-prime-strips (`FPrimeStripEquiv`), the
  prime-strip link component of the input prime-strip link;
* **APT/dsc** shape: `HodgeTheaterLink` (theater-to-theater transport data,
  used as the descent/algorithmic-parallel-transport reference);
* **HDD substrate**: the `PrimeStripSystem` carried by a `Full` theater
  (hull+det operates on prime-strip/Gaussian data).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1IPLAPTRefActual

open LeanFormal.IUT

noncomputable section

universe u

/-- IPL reference: an F-prime-strip equivalence (prime-strip link shape). -/
abbrev iplPrimeStripEquiv {V : Type u} (F F' : FPrimeStrip V) : Type u :=
  FPrimeStripEquiv F F'

theorem iplPrimeStripEquiv_refl {V : Type u} (F : FPrimeStrip V) :
    iplPrimeStripEquiv F F :=
  FPrimeStripEquiv.refl F

/-- APT/dsc reference: a link between two Hodge theaters. -/
abbrev aptTheaterLink {l : PrimeGeFive} {V : Type u}
    (S T : HodgeTheater l V) : Type u :=
  HodgeTheaterLink S T

theorem aptTheaterLink_refl {l : PrimeGeFive} {V : Type u}
    (S : HodgeTheater l V) : aptTheaterLink S S :=
  HodgeTheaterLink.refl S

/-- dsc reference: the same theater link read as a descent/transport datum. -/
abbrev dscTheaterTransport {l : PrimeGeFive} {V : Type u}
    (S T : HodgeTheater l V) : Type u :=
  HodgeTheaterLink S T

/-- HDD substrate: the `PrimeStripSystem` carried by a `Full` theater. -/
def hddPrimeStripSystem (F : _root_.IUT.HodgeTheater.Full) :
    _root_.IUT.HodgeTheater.PrimeStripSystem F.l :=
  F.add.primeStrips

@[simp] theorem hddPrimeStripSystem_V (F : _root_.IUT.HodgeTheater.Full) :
    (hddPrimeStripSystem F).V = F.add.primeStrips.V := rfl

end

end LeanFormal.IUT.XiFPaper.Mzk1IPLAPTRefActual
