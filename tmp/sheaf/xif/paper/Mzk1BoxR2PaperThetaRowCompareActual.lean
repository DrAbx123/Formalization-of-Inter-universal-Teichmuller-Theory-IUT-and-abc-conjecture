import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

/-!
# R2: paper Theta row coefficient vs `LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound`

`LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound l logp iotaL j d oq et idag`
  = (-(j^2/(2l) * oq (et idag)) + sum_i d (et i) + 1) * logp + 4 * (j+1) * iotaL.

The paper Theta row coefficient (IV L1691-1696) is
  (-(j^2/(2l) * ord(q_{v_{idag}})) + d_I + 1) * logp,
i.e. the same expression WITHOUT the Step-V term `4*(j+1)*iotaL`.

Hence (coefficient level) the paper row is `LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound - 4*(j+1)*iotaL`,
so for `iotaL >= 0` the paper row is dominated by `LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound`; the difference
is exactly the nonnegative Step-V term.  No P6IV average is redone here.
-/

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaRowCompareActual

open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.IUTIV.Estimates

variable {E : Type*} [Fintype E]

/-- The paper Theta row coefficient: `(-(j^2/(2l)) * ord(q_v) + d_I + 1) * logp`. -/
noncomputable def paperThetaRowCoefficient (l logp : Real) (j : Nat) (dI oqslot : Real) : Real :=
  (-((j : Real) ^ 2 / (2 * l) * oqslot) + dI + 1) * logp

/-- **Exact mismatch, coefficient level**: `LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound` equals the paper row
plus the Step-V term `4*(j+1)*iotaL`, under `sum d = dI` and `oq (et idag) = oqslot`. -/
theorem collectionChoiceBound_eq_paperRow_add
    (l logp iotaL : Real) (j : Nat) (d oq : E → Real) (et : Fin (j + 1) → E)
    (idag : Fin (j + 1)) (dI oqslot : Real)
    (hd : ∑ i, d (et i) = dI) (ho : oq (et idag) = oqslot) :
    LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound l logp iotaL j d oq et idag =
      paperThetaRowCoefficient l logp j dI oqslot + 4 * ((j : Real) + 1) * iotaL := by
  unfold LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound paperThetaRowCoefficient
  rw [hd, ho]

/-- **Coefficient inequality**: for `iotaL >= 0` the paper row is bounded by
`LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound`. -/
theorem paperThetaRow_le_collectionChoiceBound
    (l logp iotaL : Real) (j : Nat) (d oq : E → Real) (et : Fin (j + 1) → E)
    (idag : Fin (j + 1)) (dI oqslot : Real)
    (hd : ∑ i, d (et i) = dI) (ho : oq (et idag) = oqslot) (hι : 0 ≤ iotaL) :
    paperThetaRowCoefficient l logp j dI oqslot ≤ LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound l logp iotaL j d oq et idag := by
  rw [collectionChoiceBound_eq_paperRow_add l logp iotaL j d oq et idag dI oqslot hd ho]
  have h4 : 0 ≤ 4 * ((j : Real) + 1) * iotaL := by positivity
  linarith

#print axioms collectionChoiceBound_eq_paperRow_add
#print axioms paperThetaRow_le_collectionChoiceBound
end LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaRowCompareActual