import LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-! # S1227: actual Core on Choice = I.family.index

Label = ℤ × ℤ.  The three operations are the actual source translations:
  ind1 g i = I.translate g.1 0 i,
  ind2 g i = I.translate 0 g.2 i,
  ind3 n i = I.translate 0 (n : ℤ) i.
The group laws follow from I.translate_zero, I.translate_add and
I.translate_commute; level is constantly 0 (the source index has no separate
level coordinate in this construction), with ind3_level the only required
level law.  No concrete initial data, no weak wrapper. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1227SourceCoreActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Actual Core on the source family index, via source translations. -/
noncomputable def sourceCore : Core (ℤ × ℤ) I.family.index where
  base := I.indexOf 0 0
  level := fun _ => 0
  ind1 g i := I.translate g.1 0 i
  ind2 g i := I.translate 0 g.2 i
  ind3 n i := I.translate 0 (n : ℤ) i
  ind1_zero := by
    intro i
    exact I.translate_zero i
  ind1_add := by
    intro g h i
    change I.translate (g + h).1 0 i =
      I.translate h.1 0 (I.translate g.1 0 i)
    rw [Prod.fst_add, I.translate_add h.1 0 g.1 0 i]
    simp
  ind1_inverse := by
    intro g i
    change I.translate (-g).1 0 (I.translate g.1 0 i) = i
    rw [I.translate_add]
    simpa using I.translate_zero i
  ind2_zero := by
    intro i
    exact I.translate_zero i
  ind2_add := by
    intro g h i
    change I.translate 0 (g + h).2 i =
      I.translate 0 h.2 (I.translate 0 g.2 i)
    rw [Prod.snd_add, I.translate_add 0 h.2 0 g.2 i]
    simp
  ind2_inverse := by
    intro g i
    change I.translate 0 (-g).2 (I.translate 0 g.2 i) = i
    rw [I.translate_add]
    simpa using I.translate_zero i
  ind3_zero := by
    intro i
    exact I.translate_zero i
  ind3_add := by
    intro m n i
    change I.translate 0 ((m + n : Nat) : ℤ) i =
      I.translate 0 (n : ℤ) (I.translate 0 (m : ℤ) i)
    rw [Nat.cast_add, I.translate_add 0 (n : ℤ) 0 (m : ℤ) i]
    push_cast
    ring_nf
  ind1_ind2_commute := by
    intro g h i
    exact I.translate_commute g.1 0 0 h.2 i
  ind1_ind3_commute := by
    intro g n i
    exact I.translate_commute g.1 0 0 (n : ℤ) i
  ind2_ind3_commute := by
    intro g n i
    exact I.translate_commute 0 g.2 0 (n : ℤ) i
  ind1_level := by intro g i; rfl
  ind2_level := by intro g i; rfl
  ind3_level := by intro n i; exact Nat.zero_le _

end LeanFormal.IUT.XiFPaper.S1227SourceCoreActual

end
