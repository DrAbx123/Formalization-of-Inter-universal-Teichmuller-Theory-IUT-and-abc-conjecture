import tmp.sheaf.xif.paper.S2480QiActual
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Galois.Basic

noncomputable section
set_option maxHeartbeats 4000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2481QiGaloisActual
open LeanFormal.IUT.XiFPaper.S2480QiActual

theorem S2481_finrank : Module.finrank ℚ F = 2 := by
  change Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {(X ^ 2 + 1 : ℚ[X])}) = 2
  rw [finrank_quotient_span_eq_natDegree]
  rw [show (1 : ℚ[X]) = C 1 by simp]
  exact Polynomial.natDegree_X_pow_add_C

#print axioms S2481_finrank

end LeanFormal.IUT.XiFPaper.S2481QiGaloisActual
end