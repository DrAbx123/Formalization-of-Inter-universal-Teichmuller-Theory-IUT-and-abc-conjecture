import tmp.sheaf.xif.paper.S494TateTwoTorsionConverseGapActual
import Mathlib.Algebra.Group.TypeTags.Basic

-- S502 audit: the quotient class/lift data do NOT force an odd q-exponent.
-- A group-level counterexample and the exact odd-lift condition are recorded.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S502OddLiftObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual
open LeanFormal.IUT.XiFPaper.S494TateTwoTorsionConverseGapActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Actual minus-one class in the Tate deck quotient is 2-torsion.
noncomputable def minusOneUnit : (ACF T b)ˣ := -1

noncomputable def minusOneDeck : FDeck T b :=
  QuotientGroup.mk (minusOneUnit T b)

theorem minusOneDeck_sq_one : minusOneDeck T b ^ 2 = 1 := by
  change (QuotientGroup.mk (minusOneUnit T b) : FDeck T b) ^ 2 = 1
  rw [pow_two, ← QuotientGroup.mk_mul]
  rw [show minusOneUnit T b * minusOneUnit T b = 1 by
    ext; simp [minusOneUnit]]
  exact QuotientGroup.mk_one _

theorem minusOneDeck_eq_one_iff :
    minusOneDeck T b = 1 ↔
      minusOneUnit T b ∈ Subgroup.zpowers (qUnit T b) :=
  QuotientGroup.eq_one_iff (minusOneUnit T b)

-- Abstract group counterexample: class data x^2=1 and lift r with
-- q^k=r^2 do not force k odd.
abbrev OddLiftModel : Type := Multiplicative (ZMod 2 × ℤ)

def modelQ : OddLiftModel := Multiplicative.ofAdd ((0 : ZMod 2), 1)
def modelX : OddLiftModel := Multiplicative.ofAdd ((1 : ZMod 2), 0)

theorem modelX_sq : modelX ^ 2 = 1 := by
  decide

theorem modelX_ne_one : modelX ≠ 1 := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  simp [modelX] at h'

theorem modelQ_pow_eq_one_iff (k : ℤ) :
    modelQ ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_zpow, modelQ] at h'
    simpa using h'
  · intro hk
    subst hk
    simp

theorem not_odd_lift_from_class_data :
    ¬ ∃ k : ℤ, Odd k ∧ modelQ ^ k = modelX ^ 2 := by
  rintro ⟨k, hkodd, hk⟩
  rw [modelX_sq, modelQ_pow_eq_one_iff] at hk
  subst hk
  norm_num at hkodd

-- Exact actual odd-lift condition.
structure OddLiftCondition where
  x : FDeck T b
  x_sq_one : x ^ 2 = 1
  r : (ACF T b)ˣ
  r_class : QuotientGroup.mk r = x
  k : ℤ
  r_sq : qUnit T b ^ k = r ^ 2
  k_odd : Odd k
  root : (ACF T b)ˣ
  root_sq : root ^ 2 = qUnit T b
  point : ConversePoint T b
  point_eq : (fSidePointComparison T b).pointEquiv
    (QuotientGroup.mk root) = Multiplicative.ofAdd point

def OddLiftConditionRequired : Prop := Nonempty (OddLiftCondition T b)

#check minusOneDeck_sq_one
#check minusOneDeck_eq_one_iff
#check not_odd_lift_from_class_data
#check OddLiftCondition
#check OddLiftConditionRequired

end LeanFormal.IUT.XiFPaper.S502OddLiftObstructionActual

end