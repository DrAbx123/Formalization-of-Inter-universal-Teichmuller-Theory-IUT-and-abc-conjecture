/- R0.3: normalized height bar and D(L).
   hBar L x := (1/[L:Q]) * Height.logHeight₁ x  (Height.logHeight₁ is UNNORMALIZED, Mathlib
     NumberTheory/Height/Basic.lean:148; ABCHeightArithmeticWeightComparison.lean:7-26 examples).
   D L := logDifferentF L = log(rootDiscr L) = log|disc L|/[L:Q]
     (Mzk1ULPaperLettersActual.logDifferentF; tower identity Mzk1HT82DiscrAssemblyActual.log_rootDiscr_eq_add).
   paper: IV L1206-1235/L1309-1313 (Def1.9 normalization), L2483-2488 (C2 normalization). -/
import Mathlib.NumberTheory.Height.Basic
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import tmp.sheaf.xif.paper.Mzk1HT82DiscrAssemblyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0BarDiscActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82DiscrAssemblyActual

variable (L : Type) [Field L] [NumberField L]

/-- R0.3 normalized height bar: (1/[L:Q]) * Height.logHeight₁. -/
noncomputable def hBar (x : L) : Real :=
  (1 / (Module.finrank ℚ L : Real)) * Height.logHeight₁ x

/-- hBar = logHeight₁ / [L:Q] (rfl 口径). -/
theorem hBar_eq_logHeight_div_deg (x : L) :
    hBar L x = Height.logHeight₁ x / (Module.finrank ℚ L : Real) := by
  unfold hBar
  ring

/-- R0.3: D(L) = logDifferentF L = log(rootDiscr L). -/
noncomputable def D : Real :=
  logDifferentF L

/-- D(L) = log rootDiscr (rfl). -/
theorem D_eq_log_rootDiscr : D L = Real.log (NumberField.rootDiscr L) := rfl

set_option maxHeartbeats 1000000 in
/-- D(L) = log|N(differentIdeal Z O_L)| / [L:Q]（tower 恒等 K=Q）。 -/
theorem D_eq_log_absNorm_differentIdeal_div :
    D L =
      Real.log ((Ideal.absNorm (differentIdeal (𝓞 ℚ) (𝓞 L)) : Nat) : Real) /
        (Module.finrank ℚ L : Real) := by
  unfold D logDifferentF
  have h := log_rootDiscr_eq_add (K := ℚ) (L := L)
  have hQ : Real.log (NumberField.rootDiscr ℚ) = 0 := by
    simp [NumberField.rootDiscr]
  rw [hQ, zero_add] at h
  exact h

#print axioms hBar_eq_logHeight_div_deg
#print axioms D_eq_log_rootDiscr
#print axioms D_eq_log_absNorm_differentIdeal_div

end LeanFormal.IUT.XiFPaper.Mzk1ULR0BarDiscActual