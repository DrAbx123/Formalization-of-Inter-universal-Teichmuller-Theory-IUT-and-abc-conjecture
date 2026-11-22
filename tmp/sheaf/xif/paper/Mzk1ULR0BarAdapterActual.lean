/- R0.3 consumer adapter: hBar / D 的对外接口（供 D1 height/cond 消费者）。
   hBar L x = logHeight₁ x / [L:Q]  (Height.logHeight₁ unnormalized; paper IV L1206-1235/L2483-2488).
   D L = logDifferentF L = log(rootDiscr L) = log|disc L|/[L:Q]。 -/
import tmp.sheaf.xif.paper.Mzk1ULR0BarDiscActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0BarAdapterActual

open LeanFormal.IUT.XiFPaper.Mzk1ULR0BarDiscActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open NumberField

variable (L : Type) [Field L] [NumberField L]

/-- adapter: hBar 的 logHeight₁/[L:Q] 形式（即 hBar_eq_logHeight_div_deg 的 re-export）。 -/
theorem hBar_adapter (x : L) :
    hBar L x = Height.logHeight₁ x / (Module.finrank ℚ L : Real) :=
  hBar_eq_logHeight_div_deg L x

/-- adapter: D = logDifferentF（rfl）。 -/
theorem D_adapter : D L = logDifferentF L := rfl

/-- adapter: D = log rootDiscr。 -/
theorem D_adapter_rootDiscr : D L = Real.log (NumberField.rootDiscr L) :=
  D_eq_log_rootDiscr L

/-- adapter: disc 归一形式（log|N(differentIdeal)|/[L:Q]）。 -/
theorem D_adapter_absNorm :
    D L = Real.log ((Ideal.absNorm (differentIdeal (𝓞 ℚ) (𝓞 L)) : Nat) : Real) /
      (Module.finrank ℚ L : Real) :=
  D_eq_log_absNorm_differentIdeal_div L

#print axioms hBar_adapter
#print axioms D_adapter
#print axioms D_adapter_rootDiscr
#print axioms D_adapter_absNorm

end LeanFormal.IUT.XiFPaper.Mzk1ULR0BarAdapterActual