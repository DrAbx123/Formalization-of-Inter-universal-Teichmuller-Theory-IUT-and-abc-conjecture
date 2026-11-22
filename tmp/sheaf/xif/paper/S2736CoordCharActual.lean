import tmp.sheaf.xif.paper.S2735CharVActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2736CoordCharActual

open MeasureTheory
open scoped NNReal
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.XiFPaper.S2734DecompUnitActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2735CharVActual
open LeanFormal.IUT.PadicFiniteCoordinateHaarScaling

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]

theorem decompVUnit_eq_unitQHom (u : ℚ_[p]ˣ) :
    decompVUnit (p := p) u =
      unitQHom (p := p) (decompVUnitInt (p := p) u) := by
  apply Units.ext
  rfl

theorem distribHaarChar_coord (u : ℚ_[p]ˣ) :
    distribHaarChar (ι → ℚ_[p]) u =
      (‖(u : ℚ_[p])‖₊) ^ Fintype.card ι := by
  let pU : ℚ_[p]ˣ := padicPrimeFieldUnit (p := p)
  set K : ℤ := (u : ℚ_[p]).valuation
  have hdecomp : u = decompVUnit (p := p) u * pU ^ K := by
    unfold decompVUnit
    calc u = u * 1 := by rw [mul_one]
      _ = u * (pU ^ (-K) * pU ^ K) := by
        rw [← zpow_add, neg_add_cancel, zpow_zero]
      _ = (u * pU ^ (-K)) * pU ^ K := by rw [mul_assoc]
  have hv : distribHaarChar (ι → ℚ_[p]) (decompVUnit (p := p) u) = 1 := by
    rw [decompVUnit_eq_unitQHom]
    exact unitQ_char_eq_one (p := p) (decompVUnitInt (p := p) u)
  have hp : distribHaarChar (ι → ℚ_[p]) (pU ^ K) =
      (((p : ℝ≥0) ^ Fintype.card ι)⁻¹) ^ K := by
    rw [map_zpow, distribHaarChar_prime_finiteCoordinates]
  rw [hdecomp, map_mul, hv, hp, one_mul]
  apply NNReal.coe_injective
  push_cast
  rw [NNReal.coe_zpow, NNReal.coe_zpow, NNReal.coe_inv, NNReal.coe_pow]
  rw [← NNReal.coe_zpow]
  rw [NNReal.coe_nnnorm]
  rw [Padic.norm_eq_zpow_neg_valuation (Units.ne_zero u)]
  rw [inv_zpow]
  rw [zpow_natCast]
  ring_nf

#check distribHaarChar_coord
end LeanFormal.IUT.XiFPaper.S2736CoordCharActual
end
