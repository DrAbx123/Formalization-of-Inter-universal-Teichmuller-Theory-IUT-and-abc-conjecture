import tmp.sheaf.xif.paper.Mzk1WQMembershipTransferActual
import PadicField.FieldNorm
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1WQPadicIntegersBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped Valued

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem padicNrm_self (y : ℚ_[5]) :
    PadicField.nrm 5 ℚ_[5] y = ‖y‖ := by
  simpa using (PadicField.nrm_algebraMap (p := 5) (K := ℚ_[5]) y)

noncomputable def padicIntegersEquivMainline :
    PadicField.Integers 5 ℚ_[5] ≃+*
      (NormedField.valuation (K := ℚ_[5])).integer where
  toFun x := ⟨x, by
    rw [mem_integers_iff]
    have hx : PadicField.nrm 5 ℚ_[5] (x : ℚ_[5]) ≤ 1 := by
      rw [← PadicField.mem_integers]
      exact x.property
    simpa [padicNrm_self] using hx⟩
  invFun x := ⟨x, by
    rw [PadicField.mem_integers]
    have hx : ‖(x : ℚ_[5])‖ ≤ 1 := (mem_integers_iff (x : ℚ_[5])).mp x.property
    simpa [padicNrm_self] using hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl


end LeanFormal.IUT.XiFPaper.Mzk1WQPadicIntegersBridgeActual