import tmp.sheaf.xif.paper.Mzk1P5LabelShiftActual

/-!
# CONDITIONAL (named phase data): P5 phase/qRoot relation (CJ-L)

This file records the exact phase relation requested by P5-A8/A9:

  c_j * phase_j * qRoot^((l+1)*n) = 1,   n = thetaLabelExponent j ^ 2.

The relation is a named field here, not derived from the bridge yet.  The
derivation needs the map-zpow step from root_image and the cancellation with
qRoot^n; that remains the exact GAP.  phase_pow records phase_j^(2l)=1.

No c_j=1 theorem is asserted; this is the corrected (CJ-L) form.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5PhaseRelationActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual

universe u v

/-- Named phase/qRoot data for the corrected relation. -/
structure P5PhaseRelationData (R : Type v) [Field R] (l : PrimeGeFive) where
  qRoot : R
  qRoot_ne_zero : qRoot ≠ 0
  c : ThetaLabel (l := l) → R
  phase : ThetaLabel (l := l) → R
  phase_pow : ∀ j, phase j ^ (2 * l.value) = 1
  relation : ∀ j : ThetaLabel (l := l),
    c j * phase j * qRoot ^ ((l.value + 1) * Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2) = 1

variable {R : Type v} [Field R] {l : PrimeGeFive}
variable (D : P5PhaseRelationData R l)

/-- The named relation projects exactly, with all constants explicit. -/
theorem p5_phase_relation (j : ThetaLabel (l := l)) :
    D.c j * D.phase j * D.qRoot ^ ((l.value + 1) * Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2) = 1 :=
  D.relation j

/-- phase_j is a 2l-th root of unity. -/
theorem p5_phase_pow (j : ThetaLabel (l := l)) :
    D.phase j ^ (2 * l.value) = 1 := D.phase_pow j

#print axioms p5_phase_relation
#print axioms p5_phase_pow

end LeanFormal.IUT.XiFPaper.Mzk1P5PhaseRelationActual
