import tmp.sheaf.xif.paper.Mzk1P5BridgeIntegrationActual
import tmp.sheaf.xif.paper.Mzk1P5PhaseRelationActual

/-!
# Deriving the phase/qRoot relation from root_image

This file upgrades the named phase field of P5PhaseRelationActual as far as
possible.  It proves

  toRoot (r^N) = qRoot^((l)*N)          (root_image_zpow)

from root_image : toRoot r = qRoot^l using map_zpow.  The residual phase
relation is then derived conditionally on the paper root-unit identification
thetaUnit_j = qRoot^(j^2); the constants c_j remain explicit.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5PhaseDerivedActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual
open LeanFormal.IUT.Foundations.Theta

universe u v

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {R : Type v} [Field R] {l : PrimeGeFive}
variable (B : P5AnalyticRootBridge L R l)

/-- root_image lifted to all integral powers via map_zpow. -/
theorem root_image_zpow (N : Int) :
    B.toRoot (B.r ^ N) = (B.qRoot : R) ^ ((l.value : Int) * N) := by
  rw [map_zpow₀, B.root_image]
  have hcast : ((B.qRoot : R) ^ l.value) = ((B.qRoot : R) ^ (l.value : Int)) :=
    (zpow_natCast (B.qRoot : R) l.value).symm
  rw [hcast, ← zpow_mul]

#print axioms root_image_zpow


/-- Conditional derivation of the phase relation from root_image and the
paper root-unit identification thetaUnit_j = qRoot^(j^2). -/
theorem phase_relation
    (hunit : ∀ j : ThetaLabel (l := l),
      B.thetaUnit j = (B.qRoot : R) ^
        (Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2))
    (j : ThetaLabel (l := l)) :
    (B.c j : R) * (B.phase j : R) *
      (B.qRoot : R) ^ ((l.value + 1 : Int) *
        Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2) = 1 := by
  let n : Int := Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2
  have hz := root_image_zpow (B := B) (-n)
  have hcomp := B.comparison j
  have htheta := hunit j
  have hq0 : (B.qRoot : R) ≠ 0 := Units.ne_zero _
  have h1 : (B.qRoot : R) ^ ((l.value : Int) * -n) =
      (B.c j : R) * (B.phase j : R) * (B.qRoot : R) ^ n := by
    rw [← hz, hcomp, htheta]
  have h2 : (B.qRoot : R) ^ ((l.value : Int) * -n) *
      (B.qRoot : R) ^ ((l.value : Int) * n) = 1 := by
    rw [← zpow_add₀ hq0]
    have : (l.value : Int) * -n + (l.value : Int) * n = 0 := by ring
    rw [this, zpow_zero]
  have hsplit : (B.qRoot : R) ^ ((l.value + 1 : Int) * n) =
      (B.qRoot : R) ^ n * (B.qRoot : R) ^ ((l.value : Int) * n) := by
    rw [← zpow_add₀ hq0]
    congr 1
    ring
  rw [hsplit]
  have htarget : (B.c j : R) * (B.phase j : R) *
      ((B.qRoot : R) ^ n * (B.qRoot : R) ^ ((l.value : Int) * n)) =
      ((B.c j : R) * (B.phase j : R) * (B.qRoot : R) ^ n) *
        (B.qRoot : R) ^ ((l.value : Int) * n) := by ring
  rw [htarget, ← h1]
  exact h2

#print axioms phase_relation

end LeanFormal.IUT.XiFPaper.Mzk1P5PhaseDerivedActual
