import tmp.sheaf.xif.paper.Mzk1P5PhaseDerivedActual

/-!
# P5: c_j=1 condition derived from phase_relation

Under hunit : thetaUnit_j = qRoot^(j^2), phase_relation gives
c_j*phase_j*qRoot^((l+1)n)=1.  Hence c_j=1 is equivalent to
phase_j*qRoot^((l+1)n)=1.  This is a theorem, not a structure field.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P5CJDerivedActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PhaseDerivedActual
open LeanFormal.IUT.Foundations.Theta

universe u v

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {R : Type v} [Field R] {l : PrimeGeFive}
variable (B : P5AnalyticRootBridge L R l)
theorem c_eq_one_iff
    (hunit : ∀ j : ThetaLabel (l := l),
      B.thetaUnit j = (B.qRoot : R) ^
        (Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2))
    (j : ThetaLabel (l := l)) :
    (B.c j : R) = 1 ↔
      (B.phase j : R) * (B.qRoot : R) ^ ((l.value + 1 : Int) *
        Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2) = 1 := by
  have hrel := phase_relation (B := B) hunit j
  constructor
  · intro hc
    rw [hc, one_mul] at hrel
    simpa [mul_assoc] using hrel
  · intro hp
    have h : (B.c j : R) *
        ((B.phase j : R) * (B.qRoot : R) ^ ((l.value + 1 : Int) *
          Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2)) = 1 := by
      simpa [mul_assoc] using hrel
    rw [hp, mul_one] at h
    exact h

#print axioms c_eq_one_iff

end LeanFormal.IUT.XiFPaper.Mzk1P5CJDerivedActual
