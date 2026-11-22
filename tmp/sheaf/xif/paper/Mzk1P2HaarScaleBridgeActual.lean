import tmp.sheaf.xif.paper.Mzk1P2DetHaarProofActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
/-! P2 Haar scale bridge status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2HaarScaleBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarProofActual
open MeasureTheory MeasureTheory.Measure
def haarScaleBridgeRows : List String :=
  [ "scalar factor = lattice image mass", "central scalar p^m via FinitePadicHaarScaling",
    "SNF composition missing" ]
theorem haarScaleBridgeRows_length : haarScaleBridgeRows.length = 3 := rfl

/-- Actual scalar factor = coordLattice image mass. -/
theorem haarScaleBridge_scalar_eq_image {p : Nat} [Fact p.Prime]
    {d : Type} [Fintype d] [DecidableEq d]
    [MeasurableSpace (d -> ℚ_[p])] [BorelSpace (d -> ℚ_[p])]
    (L : (d -> ℚ_[p]) ≃L[ℚ_[p]] (d -> ℚ_[p])) :
    addHaarScalarFactor ((p2Haar (p := p) (d := d)).map L)
        (p2Haar (p := p) (d := d)) =
      ((p2Haar (p := p) (d := d)).map L)
        (coordLattice (p := p) (d := d)) :=
  p2_scalar_eq_lattice_image L
end LeanFormal.IUT.XiFPaper.Mzk1P2HaarScaleBridgeActual
end
