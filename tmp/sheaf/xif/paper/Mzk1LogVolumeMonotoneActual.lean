import tmp.sheaf.xif.paper.RefGogopexRealLineCopyActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.RefGogopexPilotComparisonActual

/-! # Log-volume monotonicity under positive transports -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LogVolumeMonotoneActual

open Iut Iut.RealLineCopy Iut.RealLineCopy.Transport Iut.Stage1

/-- Positive rescaling preserves the signed order of real log-volumes. -/
theorem signed_le_signed_of_le_mul {source target : Copy} (f : Transport source target)
    {theta q : Real} (h : q ≤ theta) : -(f.scale.val * theta) ≤ -(f.scale.val * q) := by
  have hnonneg : (0 : Real) ≤ f.scale.val := le_of_lt f.scale.pos
  have hmul : f.scale.val * q ≤ f.scale.val * theta :=
    mul_le_mul_of_nonneg_left h hnonneg
  linarith

/-- A positive transport preserves `Corollary312Inequality` of pilot log-volumes. -/
theorem transport_preserves_corollary312Inequality {source target : Copy}
    (f : Transport source target) {theta q : PilotLogVolume}
    (h : Corollary312Inequality theta q) :
    Corollary312Inequality
      ⟨theta.side, f.scale.val * theta.value⟩
      ⟨q.side, f.scale.val * q.value⟩ := by
  unfold Corollary312Inequality at *
  nlinarith [h, f.scale.pos]

/-- The absolute log-volume of a transported point is the scaled absolute value. -/
theorem transported_abs {source target : Copy} (f : Transport source target)
    (x : Point source) : |(Transport.map f x).coord| = f.scale.val * |x.coord| := by
  rw [Transport.map_coord, abs_mul, abs_of_pos f.scale.pos]

end LeanFormal.IUT.XiFPaper.Mzk1LogVolumeMonotoneActual
