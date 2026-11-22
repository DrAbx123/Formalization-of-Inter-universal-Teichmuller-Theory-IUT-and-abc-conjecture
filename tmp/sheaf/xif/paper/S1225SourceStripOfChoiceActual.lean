import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
/-! # S1225: actual stripOfChoice for arbitrary OriginalInput
For every I : OriginalInput l V, Choice := I.family.index maps to the actual
F-prime-strip at the (n,m) determined by I.index_equiv.  No concrete initial
data, no weak wrapper. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1225SourceStripOfChoiceActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
/-- Actual strip attached to a family index: the F-prime-strip at its (n,m). -/
def stripOfChoice (i : I.family.index) : FPrimeStrip.{umon, uv, upi} V :=
  I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2
@[simp] theorem stripOfChoice_indexOf (n m : Int) :
    stripOfChoice I (I.indexOf n m) = I.fPrimeStripAt n m := by
  unfold stripOfChoice
  rw [I.indexOf_apply]
theorem stripOfChoice_eq_theater (i : I.family.index) :
    stripOfChoice I i = (I.family.theater i).primeStrip := by
  unfold stripOfChoice
  rw [I.fPrimeStripAt_eq]
  rw [show I.indexOf (I.index_equiv i).1 (I.index_equiv i).2 = i by
    unfold indexOf
    exact Equiv.symm_apply_apply I.index_equiv i]
end LeanFormal.IUT.XiFPaper.S1225SourceStripOfChoiceActual
