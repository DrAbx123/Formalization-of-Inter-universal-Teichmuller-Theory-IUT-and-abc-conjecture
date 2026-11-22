import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesComponentsShaActual
import Mathlib.Tactic

/-! # Gap2 shape decomposition / relation to ABC strength -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap2ShapeDecompositionShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesComponentsShaActual

/-- Gap2 shape (arbitrary volume/weight/theta) is exactly the volume-estimate
component with weight `arithmeticWeight (abcRationalPoint a c)`. -/
theorem gap2_shape_iff_volumeEstimate (v : Nat → Nat → Nat → Real) (theta : Real) :
    (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        v a b c ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + theta + D)
      ↔ VolumeEstimate v theta :=
  Iff.rfl

/-- The absorbed form (`v - theta`) is the same Gap2 volume estimate. -/
theorem gap2_absorbed_iff_volumeEstimate (v : Nat → Nat → Nat → Real) (theta : Real) :
    (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        v a b c - theta ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + D)
      ↔
    (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        v a b c ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + theta + D) := by
  constructor
  · intro h epsilon hepsilon
    obtain ⟨D, hD⟩ := h epsilon hepsilon
    exact ⟨D, fun a b c habc => by linarith [hD a b c habc]⟩
  · intro h epsilon hepsilon
    obtain ⟨D, hD⟩ := h epsilon hepsilon
    exact ⟨D, fun a b c habc => by linarith [hD a b c habc]⟩

#print axioms gap2_shape_iff_volumeEstimate

end LeanFormal.IUT.XiFPaper.Mzk1Gap2ShapeDecompositionShaActual
