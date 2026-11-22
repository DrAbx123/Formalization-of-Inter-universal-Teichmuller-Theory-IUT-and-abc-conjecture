import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import tmp.sheaf.takkun.IutLean.Frobenioid.PrimeStripSystem

/-! Mainline (A500): adapter from our `FPrimeStrip` (IUTI/HodgeTheater/PrimeStripCore)
  to the Takkun port `IUT.Frobenioid.FhPrimeStrip` (G/Mon/action), plus the induced
  equiv adapter.  The Takkun object keeps only the local monoid + Mon + action, so we
  forget our Pi-projection, G-quotient proj, and degree data, using our `Pi` as the
  Takkun `G` (the action is on `Mon` and is the same map).

Reused object: Takkun `FhPrimeStrip` / `FhPrimeStripEquiv` (definitions + refl/symm/trans
from `tmp/sheaf/takkun/IutLean/Frobenioid/PrimeStripSystem.lean`).
No sorry/axiom. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TakkunPrimeStripAdapterActual

noncomputable section

universe u v

open LeanFormal.IUT

/-- Forget our `FPrimeStrip` into the Takkun `FhPrimeStrip`: Takkun `G := our Pi`,
  Takkun `Mon := our Mon`, Takkun `action := our action`. -/
def takkunFhOfOur {V : Type*} (F : FPrimeStrip V) :
    IUT.Frobenioid.FhPrimeStrip V where
  G := F.toDPrimeStrip.Pi
  group := F.groupPi
  Mon := F.Mon
  commMonoidMon := F.commMonoidMon
  action := F.action

@[simp] theorem takkunFhOfOur_G {V : Type*} (F : FPrimeStrip V) (x : V) :
    (takkunFhOfOur F).G x = F.toDPrimeStrip.Pi x :=
  rfl

@[simp] theorem takkunFhOfOur_Mon {V : Type*} (F : FPrimeStrip V) (x : V) :
    (takkunFhOfOur F).Mon x = F.Mon x :=
  rfl

/-- The induced equiv adapter: our `FPrimeStripEquiv` gives a Takkun
  `FhPrimeStripEquiv` (Takkun `isoG := our isoPi`, `isoMon`, `compat := compatAction`). -/
def takkunFhEquivOfOur {V : Type*} {F G : FPrimeStrip V}
    (phi : FPrimeStripEquiv F G) :
    IUT.Frobenioid.FhPrimeStripEquiv (takkunFhOfOur F) (takkunFhOfOur G) where
  isoG := phi.isoPi
  isoMon := phi.isoMon
  compat := phi.compatAction

/-- Takkun refl equiv on the image of the adapter (consumer sanity check). -/
def takkunFhEquivRefl {V : Type*} (F : FPrimeStrip V) :
    IUT.Frobenioid.FhPrimeStripEquiv (takkunFhOfOur F) (takkunFhOfOur F) :=
  IUT.Frobenioid.FhPrimeStripEquiv.refl _

end

end LeanFormal.IUT.XiFPaper.Mzk1TakkunPrimeStripAdapterActual