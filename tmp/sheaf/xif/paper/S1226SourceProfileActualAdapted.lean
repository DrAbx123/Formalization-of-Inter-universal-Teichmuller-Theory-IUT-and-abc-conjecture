import LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
/-! # S1226: actual Core/Profile on I.family.index
Core operations are the actual lattice shifts through I.index_equiv.
Profile logVolume is the actual thetaPacket.logVolume of the theater at i;
possibleImage is the singleton of that logVolume.  All four Profile laws
are proved using I.linkAt_q/scale (theta packets agree on linked theaters). -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1226SourceProfileActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
theorem indexOf_index_equiv (i : I.family.index) :
    I.indexOf (I.index_equiv i).1 (I.index_equiv i).2 = i := by
  unfold indexOf
  exact Equiv.symm_apply_apply I.index_equiv i
noncomputable def sourceCore : Core (ℤ × ℤ) I.family.index where
  base := I.indexOf 0 0
  level := fun _ => 0
  ind1 g i := I.indexOf ((I.index_equiv i).1 + g.1) (I.index_equiv i).2
  ind2 g i := I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + g.2)
  ind3 n i := I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + (n : ℤ))
  ind1_zero := by
    intro i
    change I.indexOf ((I.index_equiv i).1 + (0 : ℤ)) (I.index_equiv i).2 = i
    rw [add_zero, indexOf_index_equiv]
  ind1_add := by
    intro g h i
    change I.indexOf ((I.index_equiv i).1 + (g + h).1) (I.index_equiv i).2 =
      I.indexOf ((I.index_equiv (I.indexOf ((I.index_equiv i).1 + g.1) (I.index_equiv i).2)).1 + h.1)
        (I.index_equiv (I.indexOf ((I.index_equiv i).1 + g.1) (I.index_equiv i).2)).2
    rw [I.indexOf_apply]
    congr 1
    ring
  ind1_inverse := by
    intro g i
    change I.indexOf ((I.index_equiv (I.indexOf ((I.index_equiv i).1 + g.1) (I.index_equiv i).2)).1 + (-g).1)
        (I.index_equiv (I.indexOf ((I.index_equiv i).1 + g.1) (I.index_equiv i).2)).2 = i
    rw [I.indexOf_apply]
    simp only [Prod.fst, Prod.snd]
    rw [show (I.index_equiv i).1 + g.1 + -g.1 = (I.index_equiv i).1 by ring]
    exact indexOf_index_equiv I i
  ind2_zero := by
    intro i
    change I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + (0 : ℤ)) = i
    rw [add_zero, indexOf_index_equiv]
  ind2_add := by
    intro g h i
    change I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + (g + h).2) =
      I.indexOf (I.index_equiv (I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + g.2))).1
        ((I.index_equiv (I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + g.2))).2 + h.2)
    rw [I.indexOf_apply]
    congr 1
    ring
  ind2_inverse := by
    intro g i
    change I.indexOf (I.index_equiv (I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + g.2))).1
        ((I.index_equiv (I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + g.2))).2 + (-g).2) = i
    rw [I.indexOf_apply]
    simp only [Prod.fst, Prod.snd]
    rw [show (I.index_equiv i).2 + g.2 + -g.2 = (I.index_equiv i).2 by ring]
    exact indexOf_index_equiv I i
  ind3_zero := by
    intro i
    change I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + (0 : ℤ)) = i
    rw [add_zero, indexOf_index_equiv]
  ind3_add := by
    intro m n i
    change I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + ((m + n : Nat) : ℤ)) =
      I.indexOf (I.index_equiv (I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + (m : ℤ)))).1
        ((I.index_equiv (I.indexOf (I.index_equiv i).1 ((I.index_equiv i).2 + (m : ℤ)))).2 + (n : ℤ))
    rw [I.indexOf_apply]
    congr 1
    push_cast
    ring
  ind1_ind2_commute := by
    intro g h i
    rfl
  ind1_ind3_commute := by
    intro g n i
    rfl
  ind2_ind3_commute := by
    intro g n i
    change I.indexOf (I.index_equiv i).1 (((I.index_equiv i).2 + (n : ℤ)) + g.2) =
      I.indexOf (I.index_equiv i).1 (((I.index_equiv i).2 + g.2) + (n : ℤ))
    congr 1
    ring
  ind1_level := by intro g c; rfl
  ind2_level := by intro g c; rfl
  ind3_level := by intro n c; exact Nat.zero_le _
end LeanFormal.IUT.XiFPaper.S1226SourceProfileActualAdapted
