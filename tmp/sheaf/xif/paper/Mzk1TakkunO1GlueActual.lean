import tmp.sheaf.takkun.IutLean.Frobenioid.PrimeStrip
import tmp.sheaf.takkun.IutLean.Frobenioid.PrimeStripSystem
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import tmp.sheaf.xif.paper.Mzk1TakkunPrimeStripAdapterActual

/-!
# O1 glue: Takkun per-place Frobenioid `Model` degree and our `FPrimeStrip` image

Reuses the green Takkun module `Frobenioid/PrimeStrip` (structure `PrimeStrip` with
`loc : V -> Model`, `totalDegree`) and `Frobenioid/PrimeStripSystem`
(`FhPrimeStrip`, `FhPrimeStripEquiv`), together with our green adapter
`Mzk1TakkunPrimeStripAdapterActual`.  Exposes the O1 (BPS/prime-strip) bridge:
global degree read off the Takkun models, and the `G`/`Mon` projections of the
adapter image of our `FPrimeStrip`.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TakkunO1GlueActual

open LeanFormal.IUT

noncomputable section

universe u

/-- O1: global arithmetic degree of a Takkun prime-strip, computed from the
per-place Frobenioid models `loc v : Model`. -/
def o1GlobalDegree {V : Type u} (P : _root_.IUT.Frobenioid.PrimeStrip V)
    (s : Finset V) (x : ∀ v, (P.loc v).base.valueMonoid) : Real :=
  P.totalDegree s x

theorem o1GlobalDegree_eq {V : Type u} (P : _root_.IUT.Frobenioid.PrimeStrip V)
    (s : Finset V) (x : ∀ v, (P.loc v).base.valueMonoid) :
    o1GlobalDegree P s x = ∑ v ∈ s, (P.loc v).degree (x v) :=
  rfl

/-- O1: our `FPrimeStrip` maps into the Takkun `FhPrimeStrip` image (green adapter). -/
def o1FhOfOur {V : Type u} (F : FPrimeStrip V) :
    _root_.IUT.Frobenioid.FhPrimeStrip V :=
  LeanFormal.IUT.XiFPaper.Mzk1TakkunPrimeStripAdapterActual.takkunFhOfOur F

@[simp] theorem o1FhOfOur_G {V : Type u} (F : FPrimeStrip V) (v : V) :
    (o1FhOfOur F).G v = F.toDPrimeStrip.Pi v :=
  rfl

@[simp] theorem o1FhOfOur_Mon {V : Type u} (F : FPrimeStrip V) (v : V) :
    (o1FhOfOur F).Mon v = F.Mon v :=
  rfl

end

end LeanFormal.IUT.XiFPaper.Mzk1TakkunO1GlueActual
