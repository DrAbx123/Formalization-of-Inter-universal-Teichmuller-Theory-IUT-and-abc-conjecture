import tmp.sheaf.xif.paper.S2735CharVActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2736aCharPKActual

open MeasureTheory
open scoped NNReal
open LeanFormal.IUT.PadicFiniteCoordinateHaarScaling

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]

theorem char_pK (K : ℤ) :
    distribHaarChar (ι → ℚ_[p])
      (padicPrimeFieldUnit (p := p) ^ K) =
      (((p : ℝ≥0) ^ Fintype.card ι)⁻¹) ^ K := by
  rw [map_zpow, distribHaarChar_prime_finiteCoordinates]


theorem norm_pK (K : ℤ) :
    (‖(((padicPrimeFieldUnit (p := p) : ℚ_[p]) ^ K))‖₊) ^
        Fintype.card ι =
      (((p : ℝ≥0) ^ Fintype.card ι)⁻¹) ^ K := by
  apply NNReal.coe_injective
  push_cast
  rw [norm_zpow]
  change (‖(p : ℚ_[p])‖ ^ K) ^ Fintype.card ι = _
  rw [Padic.norm_p]
  have hbase : ((↑p : ℝ)⁻¹ ^ K) = ((↑p : ℝ) ^ K)⁻¹ := by
    rw [inv_zpow]
  have hnegL : ((↑p : ℝ) ^ K)⁻¹ = (↑p : ℝ) ^ (-K) :=
    (zpow_neg (↑p : ℝ) K).symm
  have hL : (((↑p : ℝ)⁻¹ ^ K) ^ Fintype.card ι) =
      (↑p : ℝ) ^ (-(K * (Fintype.card ι : ℤ))) := by
    rw [← zpow_natCast (a := ((↑p : ℝ)⁻¹ ^ K)) (n := Fintype.card ι)]
    rw [hbase, hnegL]
    exact (zpow_mul (↑p : ℝ) (-K) (Fintype.card ι : ℤ)).symm.trans
      (by congr 1; ring)
  have hnegR : ((↑p : ℝ) ^ (Fintype.card ι : ℤ))⁻¹ =
      (↑p : ℝ) ^ (-(Fintype.card ι : ℤ)) := by
    rw [zpow_natCast]
    exact (zpow_neg (↑p : ℝ) (Fintype.card ι : ℤ)).symm
  have hR : (((↑p : ℝ) ^ Fintype.card ι)⁻¹ ^ K) =
      (↑p : ℝ) ^ (-(K * (Fintype.card ι : ℤ))) := by
    rw [← zpow_natCast (a := (↑p : ℝ)) (n := Fintype.card ι)]
    rw [hnegR]
    exact (zpow_mul (↑p : ℝ) (-(Fintype.card ι : ℤ)) K).symm.trans
      (by congr 1; ring)
  rw [hL, hR]

#check norm_pK

#check char_pK
end LeanFormal.IUT.XiFPaper.S2736aCharPKActual
end
