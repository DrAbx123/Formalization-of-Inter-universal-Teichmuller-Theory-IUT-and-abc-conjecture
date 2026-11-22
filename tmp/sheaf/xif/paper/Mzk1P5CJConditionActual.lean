import tmp.sheaf.xif.paper.Mzk1P5PhaseRelationActual

/-!
# CONDITIONAL: c_j = 1 condition under the named phase relation

Under P5PhaseRelationData (relation c_j*phase_j*qRoot^((l+1)n)=1),
c_j=1 is equivalent to phase_j*qRoot^((l+1)n)=1.  This is the exact
condition, not a claim that c_j is 1.  The relation is named data, not derived
from the bridge here.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P5CJConditionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PhaseRelationActual

universe v

variable {R : Type v} [Field R] {l : PrimeGeFive}
variable (D : P5PhaseRelationData R l)

theorem p5_c_eq_one_iff (j : ThetaLabel (l := l)) :
    D.c j = 1 ↔
      D.phase j * D.qRoot ^ ((l.value + 1) *
        Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2) = 1 := by
  constructor
  · intro hc
    have h := D.relation j
    rw [hc, one_mul] at h
    simpa [mul_assoc] using h
  · intro hp
    have h : D.c j * (D.phase j *
        D.qRoot ^ ((l.value + 1) *
          Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2)) = 1 := by
      simpa [mul_assoc] using D.relation j
    rw [hp, mul_one] at h
    exact h

#print axioms p5_c_eq_one_iff

end LeanFormal.IUT.XiFPaper.Mzk1P5CJConditionActual
