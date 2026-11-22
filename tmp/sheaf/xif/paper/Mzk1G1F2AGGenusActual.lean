import tmp.sheaf.xif.paper.Mzk1G1F2AGWiringActual
import tmp.sheaf.xif.paper.AG02GenusActual
import Mathlib.Tactic
/-!
# F2.1 AG wiring: genus interface for the Fermat curve

Attaches `AG02GenusActual.S3133GenusInterface` to henry's `S3133CurveOver ℚ` instance
`Mzk1G1F2AGWiringActual.fermatCurveStructure (n) (hn) (hgc)` (DONE 13:31:18), where
`hgc : GeometricallyConnected (fermatCurveToSpec n)` is the only remaining explicit
instance (general-K geometric connectedness; `kbar_connected` covers k=ℚ̄ only).

## Reuse / donor check (2026-11-17)
* `Mzk1G1F2AGWiringActual.fermatCurveStructure` DONE 13:31:18;
* `AG02GenusActual.S3133GenusInterface`/`S3133Genus`/`S3133Genus_eq` (olean present);
* `AG10CanonicalDivisorGenusActual.ag10Genus` and `AG12CechRiemannRochActual.ag12_cechRiemannRoch`
  are the conditional RR consumers (need function field `K F`/`IsCurveOver`/`RiemannGenusReachedAt`).

**Not proved here**: the cohomological genus and `RiemannGenusReachedAt`; genus is explicit data.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2AGGenusActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2AGWiringActual
open LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual
open LeanFormal.IUT.XiFPaper.AG02GenusActual

/-- Genus interface attached to an explicit genus value (honest data). -/
noncomputable def S3133GenusInterface.ofGenus
    {k : Type} [Field k] (C : S3133CurveOver k) (g : Nat) :
    S3133GenusInterface C :=
  ⟨g⟩

/-- The Fermat curve's genus interface, given the explicit geometric-connectedness
instance and an explicit genus value. -/
noncomputable def fermatCurveGenusInterface (n : Nat) (hn : 0 < n)
    (hgc : GeometricallyConnected (fermatCurveToSpec n)) (g : Nat) :
    S3133GenusInterface (fermatCurveStructure n hn hgc) :=
  S3133GenusInterface.ofGenus (fermatCurveStructure n hn hgc) g

theorem fermatCurveGenusInterface_genus (n : Nat) (hn : 0 < n)
    (hgc : GeometricallyConnected (fermatCurveToSpec n)) (g : Nat) :
    S3133Genus (fermatCurveGenusInterface n hn hgc g) = g :=
  rfl

/-- F2.1 genus/RR data package. -/
structure F2GenusData where
  C : S3133CurveOver ℚ
  G : S3133GenusInterface C
  genusValue : Nat
  hgenus : G.genus = genusValue

def genusOf (D : F2GenusData) : Nat := S3133Genus D.G

theorem genusOf_eq_value (D : F2GenusData) : genusOf D = D.genusValue := by
  simp [genusOf, S3133Genus, D.hgenus]

#print axioms fermatCurveGenusInterface_genus
#print axioms genusOf_eq_value
end LeanFormal.IUT.XiFPaper.Mzk1G1F2AGGenusActual
end