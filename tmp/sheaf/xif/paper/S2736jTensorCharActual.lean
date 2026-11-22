import tmp.sheaf.xif.paper.S2736iTensorFinrankActual
import tmp.sheaf.xif.paper.S2736bCoordCharActual

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2736jTensorCharActual

open MeasureTheory
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.PadicFiniteCoordinateHaarScaling
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2734DecompUnitActual
open LeanFormal.IUT.XiFPaper.S2736aCharPKActual
open LeanFormal.IUT.XiFPaper.S2736bCoordCharActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2736hTensorCharPKFinalActual
open LeanFormal.IUT.XiFPaper.S2736iTensorFinrankActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]

theorem tensor_char_decompVUnit (u : ℚ_[p]ˣ) :
    distribHaarChar (FinitePadicTensor (p := p) M)
      (decompVUnit (p := p) u) = 1 := by
  rw [decompVUnit_eq_unitQHom]
  exact tensor_unit_char_eq_one (p := p) M (decompVUnitInt (p := p) u)

theorem unit_decomp (u : ℚ_[p]ˣ) :
    u = decompVUnit (p := p) u *
      padicPrimeFieldUnit (p := p) ^ (u : ℚ_[p]).valuation := by
  let pU : ℚ_[p]ˣ := padicPrimeFieldUnit (p := p)
  have hp : (↑p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  apply Units.ext
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [decompVUnit_val, decompV]
  rw [show (pU : ℚ_[p]) = (↑p : ℚ_[p]) from rfl]
  have hz : (↑p : ℚ_[p]) ^ (-((u : ℚ_[p]).valuation)) *
      (↑p : ℚ_[p]) ^ ((u : ℚ_[p]).valuation) = 1 := by
    rw [← zpow_add₀ hp]
    rw [show -((u : ℚ_[p]).valuation) + ((u : ℚ_[p]).valuation) = 0 by ring, zpow_zero]
  change (u : ℚ_[p]) = ((u : ℚ_[p]) * (↑p : ℚ_[p]) ^ (-((u : ℚ_[p]).valuation))) * (↑p : ℚ_[p]) ^ ((u : ℚ_[p]).valuation)
  rw [mul_assoc, hz, mul_one]

theorem nnnorm_decomp_mul (u : ℚ_[p]ˣ) :
    ‖(((decompVUnit (p := p) u *
      padicPrimeFieldUnit (p := p) ^ (u : ℚ_[p]).valuation : ℚ_[p])))‖₊ =
      ‖(((padicPrimeFieldUnit (p := p) ^ (u : ℚ_[p]).valuation : ℚ_[p])))‖₊ := by
  rw [nnnorm_mul, decompVUnit_norm, one_mul]

#check tensor_char_decompVUnit
#check unit_decomp

theorem tensor_char (u : ℚ_[p]ˣ) :
    distribHaarChar (FinitePadicTensor (p := p) M) u =
      (‖(u : ℚ_[p])‖₊) ^
        Module.finrank ℚ_[p] (FinitePadicTensor (p := p) M) := by
  have hdecomp := unit_decomp (p := p) u
  have hnorm := nnnorm_decomp_mul (p := p) u
  have hnorm' : ‖(↑(decompVUnit (p := p) u) *
      (↑(padicPrimeFieldUnit (p := p) ^
        (u : ℚ_[p]).valuation) : ℚ_[p]))‖₊ =
      ‖(↑(padicPrimeFieldUnit (p := p) ^
        (u : ℚ_[p]).valuation) : ℚ_[p])‖₊ := by
    simpa [Units.val_zpow_eq_zpow_val] using hnorm
  rw [hdecomp, map_mul, tensor_char_decompVUnit, one_mul]
  rw [tensor_char_pK (p := p) M ((u : ℚ_[p]).valuation)]
  rw [finrank_tensor (p := p) M]
  rw [show (↑(decompVUnit (p := p) u *
      padicPrimeFieldUnit (p := p) ^ (u : ℚ_[p]).valuation) : ℚ_[p]) =
      ↑(decompVUnit (p := p) u) *
        (↑(padicPrimeFieldUnit (p := p) ^
          (u : ℚ_[p]).valuation) : ℚ_[p]) from
    Units.val_mul (decompVUnit (p := p) u)
      (padicPrimeFieldUnit (p := p) ^ (u : ℚ_[p]).valuation)]
  rw [hnorm']
  rw [Units.val_zpow_eq_zpow_val]
  rw [nnnorm_zpow]
  rw [← zpow_natCast]
  rw [← zpow_natCast]
  rw [← zpow_mul, ← zpow_mul]
  exact congrArg (fun e : ℤ =>
    (‖(padicPrimeFieldUnit (p := p) : ℚ_[p])‖₊) ^ e) (mul_comm _ _)

#check tensor_char

#check nnnorm_decomp_mul
end LeanFormal.IUT.XiFPaper.S2736jTensorCharActual
end
