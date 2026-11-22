import tmp.sheaf.xif.paper.S1225SourceChoiceCoreActual
import LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
import Mathlib.Algebra.Group.Commute.Basic

/-! # S1231: actual Core on Choice = I.family.index

Label = ℤ.  ind1/ind2/ind3 are the S1225 actual source operations: inverse
horizontal/vertical permutation powers and the actual translate (n,0).
All 15 Core laws are actual; level is constantly 0, so ind3_level is
0 ≤ 0.  No weak wrapper and no concrete initial instance. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1231SourceCoreActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.XiFPaper.S1225SourceChoiceCoreActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev Choice : Type _ := I.family.index

theorem horizontalShift_eq_translate_one (c : Choice (I := I)) :
    I.horizontalShift c = I.translate 1 0 c := by
  apply I.index_equiv.injective
  rw [I.horizontalShift_index, I.translate_index]
  simp [horizontalIndex, translateIndex]

theorem verticalShift_eq_translate_one (c : Choice (I := I)) :
    I.verticalShift c = I.translate 0 1 c := by
  apply I.index_equiv.injective
  rw [I.verticalShift_index, I.translate_index]
  simp [verticalIndex, translateIndex]

theorem horizontalPerm_eq_translate (c : Choice (I := I)) :
    horizontalPerm I c = translatePerm I 1 c := by
  exact horizontalShift_eq_translate_one I c

theorem verticalPerm_comm_translate (n : ℤ) :
    Commute (verticalPerm I) (translatePerm I n) := by
  change verticalPerm I * translatePerm I n = translatePerm I n * verticalPerm I
  ext c
  change I.verticalShift (I.translate n 0 c) =
    I.translate n 0 (I.verticalShift c)
  rw [verticalShift_eq_translate_one I (I.translate n 0 c),
    verticalShift_eq_translate_one I c]
  exact I.translate_commute 0 1 n 0 c

theorem horizontalPerm_comm_translate (n : ℤ) :
    Commute (horizontalPerm I) (translatePerm I n) := by
  change horizontalPerm I * translatePerm I n = translatePerm I n * horizontalPerm I
  ext c
  change I.horizontalShift (I.translate n 0 c) =
    I.translate n 0 (I.horizontalShift c)
  rw [horizontalShift_eq_translate_one I (I.translate n 0 c),
    horizontalShift_eq_translate_one I c]
  exact I.translate_commute 1 0 n 0 c

theorem horizontal_vertical_perm_commute :
    Commute (horizontalPerm I) (verticalPerm I) := by
  change horizontalPerm I * verticalPerm I = verticalPerm I * horizontalPerm I
  ext c
  exact I.horizontal_vertical_shift_commute c

/-- Actual Core on the source family index. -/
noncomputable def sourceCore : Core ℤ (Choice (I := I)) where
  base := I.indexOf 0 0
  level := fun _ => 0
  ind1 g c := sourceInd1 I g c
  ind2 g c := sourceInd2 I g c
  ind3 n c := sourceInd3 I n c
  ind1_zero := by
    intro c
    simp [sourceInd1]
  ind1_add := by
    intro g h c
    unfold sourceInd1
    rw [← Equiv.Perm.mul_apply]
    congr 1
    rw [← zpow_add]
    congr 1
    ring
  ind1_inverse := by
    intro g c
    unfold sourceInd1
    rw [← Equiv.Perm.mul_apply]
    congr 1
    rw [← zpow_add]
    simp
  ind2_zero := by
    intro c
    simp [sourceInd2]
  ind2_add := by
    intro g h c
    unfold sourceInd2
    rw [← Equiv.Perm.mul_apply]
    congr 1
    rw [← zpow_add]
    congr 1
    ring
  ind2_inverse := by
    intro g c
    unfold sourceInd2
    rw [← Equiv.Perm.mul_apply]
    congr 1
    rw [← zpow_add]
    simp
  ind3_zero := by
    intro c
    simp [sourceInd3, translatePerm, I.translate_zero]
  ind3_add := by
    intro m n c
    unfold sourceInd3 translatePerm
    change I.translate ((m + n : Nat) : ℤ) 0 c =
      I.translate (n : ℤ) 0 (I.translate (m : ℤ) 0 c)
    rw [I.translate_add]
    push_cast
    ring_nf
  ind1_ind2_commute := by
    intro g h c
    unfold sourceInd1 sourceInd2
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
    have hcomm := horizontal_vertical_perm_commute I
    have h := hcomm.zpow_zpow (-g) (-h)
    simpa [Equiv.Perm.mul_apply] using congrArg (fun p : Equiv.Perm (Choice (I := I)) => p c) h
  ind1_ind3_commute := by
    intro g n c
    unfold sourceInd1 sourceInd3 translatePerm
    rw [← Equiv.Perm.mul_apply]
    have h := (horizontalPerm_comm_translate I (n : ℤ)).zpow_left (-g)
    simpa [translatePerm, Equiv.Perm.mul_apply] using
      congrArg (fun p : Equiv.Perm (Choice (I := I)) => p c) h
  ind2_ind3_commute := by
    intro g n c
    unfold sourceInd2 sourceInd3 translatePerm
    rw [← Equiv.Perm.mul_apply]
    have h := (verticalPerm_comm_translate I (n : ℤ)).zpow_left (-g)
    simpa [translatePerm, Equiv.Perm.mul_apply] using
      congrArg (fun p : Equiv.Perm (Choice (I := I)) => p c) h
  ind1_level := by intro g c; rfl
  ind2_level := by intro g c; rfl
  ind3_level := by intro n c; exact Nat.zero_le _

end LeanFormal.IUT.XiFPaper.S1231SourceCoreActual

end
