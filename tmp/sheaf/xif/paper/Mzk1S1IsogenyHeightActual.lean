import Iut.Tripod.CyclicArch

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1S1IsogenyHeightActual
open WeierstrassCurve
open Iut.Tripod

/-- Actual archimedean height-magnification data for Legendre curves with bounded
parameter, from Iut.CyclicArch.legendre_torsion_x_le. -/
structure S1IsogenyHeightData (c : ℝ) where
  C0 : ℝ
  C0_nonneg : 0 ≤ C0
  arch_bound : ∀ (l : ℂ), |Real.log ‖l‖| ≤ c → |Real.log ‖l - 1‖| ≤ c →
      ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], W = legendre l →
      ∀ {N : ℕ}, 1 ≤ N → ∀ {x y : ℂ} (h : W.toAffine.Nonsingular x y),
        N • (Affine.Point.some x y h : W.toAffine.Point) = 0 → ‖x‖ ≤ C0 * N ^ 2

def s1IsogenyHeightActual (c : ℝ) : S1IsogenyHeightData c :=
  let h := Iut.CyclicArch.legendre_torsion_x_le c
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

end LeanFormal.IUT.XiFPaper.Mzk1S1IsogenyHeightActual
end
