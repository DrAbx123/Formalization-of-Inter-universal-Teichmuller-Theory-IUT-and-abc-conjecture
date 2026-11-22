import tmp.sheaf.xif.paper.S2563DiscrMatrixActual
noncomputable section
set_option maxHeartbeats 16000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2564DiscrUnitActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2563DiscrMatrixActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
theorem discr_unit : IsUnit (algebraMap ℤ R2 (Polynomial.discr S2481HZ)) := by
  have hmul : algebraMap ℤ R2 Cden =
      algebraMap ℤ R2 c0 * algebraMap ℤ R2 (Polynomial.discr S2481HZ) := by
    unfold Cden
    rw [discr_eq]
    rw [map_mul]
    rfl
  have hu : IsUnit (algebraMap ℤ R2 c0 *
      algebraMap ℤ R2 (Polynomial.discr S2481HZ)) := by
    rw [← hmul]
    exact hCden_unit
  exact isUnit_of_mul_isUnit_right hu
#print axioms discr_unit
end LeanFormal.IUT.XiFPaper.S2564DiscrUnitActual
end
