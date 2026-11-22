import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2561Mod613Chain1ActualAdapted

open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

lemma chunk0 (n : ℕ) (hn : n ≤ 80) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    (simp [S0, G, T1, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff,
      S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, mul_add, add_mul,
      Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one,
      Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num)

end LeanFormal.IUT.XiFPaper.S2561Mod613Chain1ActualAdapted

end