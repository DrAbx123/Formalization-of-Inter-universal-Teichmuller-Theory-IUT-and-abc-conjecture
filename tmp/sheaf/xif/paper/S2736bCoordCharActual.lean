import tmp.sheaf.xif.paper.S2736aCharPKActual
import tmp.sheaf.xif.paper.S2735CharVActual
import tmp.sheaf.xif.paper.S2734LatticeActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2736bCoordCharActual

open MeasureTheory
open scoped NNReal
open LeanFormal.IUT.PadicFiniteCoordinateHaarScaling
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.XiFPaper.S2734DecompUnitActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2735CharVActual
open LeanFormal.IUT.XiFPaper.S2736aCharPKActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]

theorem decompVUnit_val (u : ℚ_[p]ˣ) :
    (decompVUnit (p := p) u : ℚ_[p]) = decompV (p := p) u := by
  simp [decompVUnit, decompV, padicPrimeFieldUnit]

theorem decompVUnit_eq_unitQHom (u : ℚ_[p]ˣ) :
    decompVUnit (p := p) u =
      unitQHom (p := p) (decompVUnitInt (p := p) u) := by
  apply Units.ext
  rw [decompVUnit_val]
  simp [unitQHom, decompVUnitInt, zv, decompV, padicIntToPadic]

theorem char_decompVUnit (u : ℚ_[p]ˣ) :
    distribHaarChar (ι → ℚ_[p]) (decompVUnit (p := p) u) = 1 := by
  rw [decompVUnit_eq_unitQHom]
  exact unitQ_char_eq_one (p := p) (decompVUnitInt (p := p) u)

theorem decompVUnit_norm (u : ℚ_[p]ˣ) :
    ‖(decompVUnit (p := p) u : ℚ_[p])‖₊ = 1 := by
  rw [decompVUnit_val]
  apply NNReal.coe_injective
  push_cast
  rw [decompV_norm_eq_one]

theorem distribHaarChar_coord (u : ℚ_[p]ˣ) :
    distribHaarChar (ι → ℚ_[p]) u = (‖(u : ℚ_[p])‖₊) ^ Fintype.card ι := by
  let pU : ℚ_[p]ˣ := padicPrimeFieldUnit (p := p)
  set K : ℤ := (u : ℚ_[p]).valuation
  have hdecomp : u = decompVUnit (p := p) u * pU ^ K := by
    apply Units.ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
    rw [decompVUnit_val, decompV]
    rw [show (pU : ℚ_[p]) = (↑p : ℚ_[p]) from rfl]
    change (u : ℚ_[p]) =
      ((u : ℚ_[p]) * (↑p : ℚ_[p]) ^ (-K)) * (↑p : ℚ_[p]) ^ K
    have hp : (↑p : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
    have hz : (↑p : ℚ_[p]) ^ (-K) * (↑p : ℚ_[p]) ^ K = 1 := by
      rw [← zpow_add₀ hp]
      rw [show -K + K = 0 by ring, zpow_zero]
    rw [mul_assoc, hz, mul_one]
  rw [hdecomp, map_mul, char_decompVUnit, one_mul, char_pK]
  rw [Units.val_mul, nnnorm_mul, decompVUnit_norm, one_mul]
  rw [Units.val_zpow_eq_zpow_val]
  rw [show (pU : ℚ_[p]) = (↑p : ℚ_[p]) from rfl]
  rw [show (↑p : ℚ_[p]) = (padicPrimeFieldUnit (p := p) : ℚ_[p]) from rfl]
  rw [norm_pK]

#check distribHaarChar_coord
end LeanFormal.IUT.XiFPaper.S2736bCoordCharActual
end
