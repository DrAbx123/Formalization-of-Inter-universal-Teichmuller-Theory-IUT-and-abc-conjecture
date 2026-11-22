import tmp.sheaf.xif.paper.Mzk1C0GlobalIdeleActual
import tmp.sheaf.xif.paper.Mzk1NormArchCKActual
import Mathlib.Tactic

/-!
# C0 idele candidate height: finite bad sum + arch sum

Constructs an explicit real functional from the idele data:
`heightWeight * (sum_bad log max(norm q_v,1) + sum_arch log max(norm arch_w,1))`.
This is NOT identified with the global hBox or qPilotLogVolumeReading; that
identification is the remaining exact gap.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1C0IdeleHeightActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1C0GlobalIdeleActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
open LeanFormal.IUT.IUTIV.Estimates
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Finite bad-prime term of the candidate height: normalized log max(norm q_v,1). -/
noncomputable def c0IdeleFiniteHeight (D : C0GlobalIdeleData T) : Real :=
  heightWeight (F := T.arithmetic.F) *
    ∑ b : Bad (nativePlaceSelection T),
      Real.log (max ‖(D.bad b : NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b))‖ 1)

/-- Arch term of the candidate height: normalized log max(norm arch_w,1). -/
noncomputable def c0IdeleArchHeight (D : C0GlobalIdeleData T) : Real :=
  heightWeight (F := T.arithmetic.F) *
    ∑ w : NumberField.InfinitePlace T.arithmetic.F,
      Real.log (max ‖((D.arch w : (w.Completion)ˣ) : w.Completion)‖ 1)

/-- Candidate idele height = finite empirical + arch empirical. -/
noncomputable def c0IdeleHeight (D : C0GlobalIdeleData T) : Real :=
  c0IdeleFiniteHeight T D + c0IdeleArchHeight T D

theorem c0IdeleHeight_eq_finite_add_arch (D : C0GlobalIdeleData T) :
    c0IdeleHeight T D = c0IdeleFiniteHeight T D + c0IdeleArchHeight T D := rfl

theorem c0IdeleHeight_eq_weight_mul_sum (D : C0GlobalIdeleData T) :
    c0IdeleHeight T D = heightWeight (F := T.arithmetic.F) *
      ((∑ b : Bad (nativePlaceSelection T),
          Real.log (max ‖(D.bad b : NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b))‖ 1)) +
        (∑ w : NumberField.InfinitePlace T.arithmetic.F,
          Real.log (max ‖((D.arch w : (w.Completion)ˣ) : w.Completion)‖ 1))) := by
  unfold c0IdeleHeight c0IdeleFiniteHeight c0IdeleArchHeight
  ring

structure C0HeightComponents (D : C0GlobalIdeleData T) (x : T.arithmetic.F) where
  finite_eq : c0IdeleFiniteHeight T D = hNon (F := T.arithmetic.F) x
  arch_eq : c0IdeleArchHeight T D = hArc (F := T.arithmetic.F) x

theorem c0IdeleHeight_eq_hBox_of_components
    (D : C0GlobalIdeleData T) (x : T.arithmetic.F)
    (h : C0HeightComponents T D x) :
    c0IdeleHeight T D = hBox (F := T.arithmetic.F) x := by
  unfold c0IdeleHeight hBox
  rw [h.finite_eq, h.arch_eq]

noncomputable def c0SignedIdeleHeight (D : C0GlobalIdeleData T) : Real :=
  -c0IdeleHeight T D

theorem c0SignedIdeleHeight_eq_neg_hBox_of_components
    (D : C0GlobalIdeleData T) (x : T.arithmetic.F)
    (h : C0HeightComponents T D x) :
    c0SignedIdeleHeight T D = -hBox (F := T.arithmetic.F) x := by
  unfold c0SignedIdeleHeight
  rw [c0IdeleHeight_eq_hBox_of_components T D x h]

theorem c0IdeleFiniteHeight_nonneg (D : C0GlobalIdeleData T) :
    0 ≤ c0IdeleFiniteHeight T D := by
  unfold c0IdeleFiniteHeight
  apply mul_nonneg
  · rw [← archCK_eq_heightWeight]
    exact (archCK_pos (K := T.arithmetic.F)).le
  · exact Finset.sum_nonneg (fun b _ => Real.log_nonneg (le_max_right _ 1))

theorem c0IdeleArchHeight_nonneg (D : C0GlobalIdeleData T) :
    0 ≤ c0IdeleArchHeight T D := by
  unfold c0IdeleArchHeight
  apply mul_nonneg
  · rw [← archCK_eq_heightWeight]
    exact (archCK_pos (K := T.arithmetic.F)).le
  · exact Finset.sum_nonneg (fun w _ => Real.log_nonneg (le_max_right _ 1))

theorem c0IdeleHeight_nonneg (D : C0GlobalIdeleData T) :
    0 ≤ c0IdeleHeight T D :=
  add_nonneg (c0IdeleFiniteHeight_nonneg T D) (c0IdeleArchHeight_nonneg T D)

#print axioms c0IdeleHeight_eq_finite_add_arch
#print axioms c0IdeleHeight_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1C0IdeleHeightActual
