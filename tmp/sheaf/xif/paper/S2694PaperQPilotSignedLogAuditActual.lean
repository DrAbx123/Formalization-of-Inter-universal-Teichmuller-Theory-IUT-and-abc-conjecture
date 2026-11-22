import tmp.sheaf.xif.paper.S1968QVDeterminedQPilotActual
import tmp.sheaf.xif.paper.S1960QPilotAnchorActual
import tmp.sheaf.xif.paper.S1527OOrderEqualityActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2694PaperQPilotSignedLogAuditActual

local instance s2694GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2694FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

variable {l : PrimeGeFive}
variable (D : S1895PaperInput)

/-- The paper q-pilot signed log, literally the source signed log of the paper
input. -/
def S2694PaperQPilotSignedLog : ℝ :=
  sourceQPilotSignedLog (paperInput D).initial

theorem S2694PaperQPilotSignedLog_eq_paperQPilotLogVolume :
    S2694PaperQPilotSignedLog D = paperQPilotLogVolume D := rfl

/-- Actual closed form: the paper q-pilot signed log is minus order_C3 times
log 5.  This is the actual value, not a normalized or chosen real. -/
theorem S2694PaperQPilotSignedLog_eq_orderC3 :
    S2694PaperQPilotSignedLog D = -((S1487Cand.order : ℝ) * Real.log 5) := by
  rw [S2694PaperQPilotSignedLog_eq_paperQPilotLogVolume]
  exact paperQPilotLogVolume_eq_orderC3 D

theorem S2694PaperQPilotSignedLog_neg : S2694PaperQPilotSignedLog D < 0 := by
  rw [S2694PaperQPilotSignedLog_eq_orderC3]
  have hpos : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have horder : (0 : ℝ) < (S1487Cand.order : ℝ) := by
    exact_mod_cast S1487Cand.order_pos
  nlinarith

/-- The absolute value is exactly the source bad-q absolute log, hence
order_C3 * log 5. -/
theorem S2694PaperQPilotSignedLog_abs :
    |S2694PaperQPilotSignedLog D| = (S1487Cand.order : ℝ) * Real.log 5 := by
  rw [S2694PaperQPilotSignedLog_eq_orderC3, abs_neg]
  have h : (0 : ℝ) ≤ (S1487Cand.order : ℝ) * Real.log 5 := by positivity
  rw [abs_of_nonneg h]

theorem S2694PaperQPilotSignedLog_le_neg_log5 :
    S2694PaperQPilotSignedLog D ≤ -Real.log 5 := by
  rw [S2694PaperQPilotSignedLog_eq_orderC3]
  have hlog : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have horder : (1 : ℝ) ≤ (S1487Cand.order : ℝ) := by
    exact_mod_cast S1487Cand.order_pos
  nlinarith

theorem S2694PaperQPilotSignedLog_ne_zero :
    S2694PaperQPilotSignedLog D ≠ 0 :=
  ne_of_lt (S2694PaperQPilotSignedLog_neg D)

/-- Exact condition for the value -log 5: the actual DVR order is one. -/
theorem S2694PaperQPilotSignedLog_eq_neg_log5_iff :
    S2694PaperQPilotSignedLog D = -Real.log 5 ↔ S1487Cand.order = 1 := by
  rw [S2694PaperQPilotSignedLog_eq_orderC3]
  constructor
  · intro h
    have hlog : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
    have hreal : (S1487Cand.order : ℝ) = 1 := by
      nlinarith
    exact_mod_cast hreal
  · intro h
    rw [h]
    norm_num

#print axioms S2694PaperQPilotSignedLog_eq_orderC3
#print axioms S2694PaperQPilotSignedLog_neg
#print axioms S2694PaperQPilotSignedLog_abs
#print axioms S2694PaperQPilotSignedLog_eq_neg_log5_iff

end LeanFormal.IUT.XiFPaper.S2694PaperQPilotSignedLogAuditActual
end
