import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- S636: exact theta normalization audit.
-- realThetaValue q j = q^(j^2).  Paper theta uses q[2u]^(j^2), where
-- q[2u] is the 2l-th root of q[1u]; using q[1u] raises paper theta to 2l.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S636ThetaNormalizationAuditActual

open LeanFormal.IUT

universe u

variable {l : PrimeGeFive}

/-- Paper q[2u]-normalized theta value: q[2u]^(j^2). -/
def paperThetaScale (qTwoU : Real) (j : SignedLabel l.value) : Real :=
  qTwoU ^ (gaussExponent j.1).toNat

theorem paperThetaScale_eq_realThetaValue (qTwoU : Real)
    (j : SignedLabel l.value) :
    paperThetaScale qTwoU j = realThetaValue qTwoU j.1 := rfl

theorem finitePacket_qTwoU_scale (qTwoU : Real) (hq : 0 < qTwoU)
    (j : SignedLabel l.value) :
    (FiniteThetaPacket.ofQ (l := l) qTwoU hq).scale j =
      paperThetaScale qTwoU j := rfl

/-- q[1u]-normalized paper theta magnitude: q[1u]^(j^2/(2l)). -/
noncomputable def paperThetaScaleFromQParameter
    (qOneU : Real) (j : SignedLabel l.value) : Real :=
  Real.rpow qOneU ((gaussExponent j.1 : Real) / (2 * l.value))

/-- Exact expected normalization identity: for q[2u]^(2l)=q[1u], the
q[1u]-rpow form agrees with q[2u]^(j^2).  Kept as a proposition. -/
def PaperThetaNormalizationIdentity : Prop :=
  ∀ (qOneU qTwoU : Real), 0 <= qTwoU →
    qOneU = qTwoU ^ (2 * l.value) →
      ∀ j : SignedLabel l.value,
        paperThetaScaleFromQParameter qOneU j = paperThetaScale qTwoU j
theorem realThetaValue_qOneU_eq_paper_pow
    (qTwoU qOneU : Real) (h : qOneU = qTwoU ^ (2 * l.value))
    (j : Int) :
    realThetaValue qOneU j = (realThetaValue qTwoU j) ^ (2 * l.value) := by
  unfold realThetaValue
  rw [h, ← pow_mul, ← pow_mul]
  congr 1
  rw [Nat.mul_comm]

theorem finitePacket_qOneU_scale_eq_paper_pow
    (qTwoU qOneU : Real) (hqTwo : 0 < qTwoU) (hqOne : 0 < qOneU)
    (h : qOneU = qTwoU ^ (2 * l.value))
    (j : SignedLabel l.value) :
    (FiniteThetaPacket.ofQ (l := l) qOneU hqOne).scale j =
      (paperThetaScale qTwoU j) ^ (2 * l.value) := by
  change realThetaValue qOneU j.1 = (qTwoU ^ (gaussExponent j.1).toNat) ^ (2 * l.value)
  rw [realThetaValue_qOneU_eq_paper_pow qTwoU qOneU h j.1]
  rfl

#check paperThetaScale
#check finitePacket_qTwoU_scale
#check realThetaValue_qOneU_eq_paper_pow
#check finitePacket_qOneU_scale_eq_paper_pow

end LeanFormal.IUT.XiFPaper.S636ThetaNormalizationAuditActual

end