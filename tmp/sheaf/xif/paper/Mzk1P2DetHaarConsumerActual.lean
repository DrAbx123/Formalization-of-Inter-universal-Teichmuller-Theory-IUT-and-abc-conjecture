import tmp.sheaf.xif.paper.Mzk1P2DetHaarProofActual
import tmp.sheaf.xif.paper.Mzk1P2DetCoefficientActual
/-! P2 det-Haar consumer status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarProofActual
open MeasureTheory MeasureTheory.Measure
def detHaarConsumerRows : List String :=
  [ "scalar factor = coordLattice image mass (green)",
    "GL and B4 pieces green",
    "consumer waits on SNF composition for arbitrary GL_d(Qp)" ]
theorem detHaarConsumerRows_length : detHaarConsumerRows.length = 3 := rfl
def detHaarConsumerMissing : List String :=
  [ "general det-Haar law for arbitrary continuous linear equivalence" ]
theorem detHaarConsumerMissing_length : detHaarConsumerMissing.length = 1 := rfl

/-- Actual fixed-Haar mass of the coordinate lattice is 1. -/
theorem detHaarConsumer_coordLattice_mass {p : Nat} [Fact p.Prime]
    {d : Type} [Fintype d] [DecidableEq d]
    [MeasurableSpace (d -> ℚ_[p])] [BorelSpace (d -> ℚ_[p])] :
    p2Haar (coordLattice (p := p) (d := d)) = 1 :=
  p2_coordLattice_mass
end LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarConsumerActual
end
