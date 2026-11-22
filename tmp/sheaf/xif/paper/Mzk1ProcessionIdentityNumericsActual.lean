import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Mzk1ProcessionIdentityNumericsActual — procession identity and constants (Unit A)

Lean transcription of the exact rational arithmetic of the mined independent verification
script 01_procession_identity (laichunwing, IUT-Verification, Unit A):
A_raw(l) = sum_{j=1}^{l*} j^2/(2l) = (l^2-1)/48, A_norm(l) = (l+1)/24,
A_raw = l* A_norm with l* = (l-1)/2; and the two constants chi = 12/(l(l+1)),
tau = 12/l^2 with chi - tau = -12/(l^2(l+1)), chi/tau = l/(l+1).
Pure real arithmetic; no structural claim.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ProcessionIdentityNumericsActual

/-- The raw procession sum closed form A_raw(l) = (l^2 - 1)/48. -/
noncomputable def processionRaw (l : Nat) : Real := ((l : Real) ^ 2 - 1) / 48

/-- The procession mean A_norm(l) = (l+1)/24. -/
noncomputable def processionNorm (l : Nat) : Real := ((l : Real) + 1) / 24

/-- With l = 2 n + 1: A_raw = n(n+1)/12. -/
theorem processionRaw_two_mul_add_one (n : Nat) :
    processionRaw (2 * n + 1) = (n : Real) * ((n : Real) + 1) / 12 := by
  unfold processionRaw
  push_cast
  ring

/-- With l = 2 n + 1: A_norm = (n+1)/12. -/
theorem processionNorm_two_mul_add_one (n : Nat) :
    processionNorm (2 * n + 1) = ((n : Real) + 1) / 12 := by
  unfold processionNorm
  push_cast
  ring

/-- The relation A_raw = l* A_norm, with l* = n for l = 2n+1. -/
theorem processionRaw_eq_lStar_mul_norm (n : Nat) :
    processionRaw (2 * n + 1) = (n : Real) * processionNorm (2 * n + 1) := by
  rw [processionRaw_two_mul_add_one, processionNorm_two_mul_add_one]
  field_simp

/-- The first constant chi = 12/(l(l+1)). -/
noncomputable def chi (l : Nat) : Real := 12 / ((l : Real) * ((l : Real) + 1))

/-- The second constant tau = 12/l^2. -/
noncomputable def tau (l : Nat) : Real := 12 / (l : Real) ^ 2

/-- chi - tau = -12/(l^2 (l+1)). -/
theorem chi_sub_tau (l : Nat) (hl : 0 < l) :
    chi l - tau l = -12 / ((l : Real) ^ 2 * ((l : Real) + 1)) := by
  unfold chi tau
  have hlR : (0 : Real) < (l : Real) := by exact_mod_cast hl
  have hl1 : (0 : Real) < (l : Real) + 1 := by linarith
  field_simp

/-- chi / tau = l/(l+1). -/
theorem chi_div_tau (l : Nat) (hl : 0 < l) :
    chi l / tau l = (l : Real) / ((l : Real) + 1) := by
  unfold chi tau
  have hlR : (0 : Real) < (l : Real) := by exact_mod_cast hl
  have hl1 : (0 : Real) < (l : Real) + 1 := by linarith
  field_simp

#check processionRaw
#check processionNorm
#check processionRaw_two_mul_add_one
#check processionNorm_two_mul_add_one
#check processionRaw_eq_lStar_mul_norm
#check chi_sub_tau
#check chi_div_tau

end LeanFormal.IUT.XiFPaper.Mzk1ProcessionIdentityNumericsActual
end
