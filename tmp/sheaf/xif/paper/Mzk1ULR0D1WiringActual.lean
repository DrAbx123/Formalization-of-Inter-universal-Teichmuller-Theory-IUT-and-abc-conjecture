/- R0.3 D1 consumer wiring: discOver = logDifferentF (=D), truncConductor normalized form, h slot = hBar.
   donor lines: Mzk1G1LocalHeightCriterionActual.lean:16-17 discOver, :29-37 truncConductor;
                Mzk1ULPaperLettersActual.logDifferentF; NumberField.rootDiscr = |disc|^(1/[K:Q]);
                IUT.ABCBridge.Arithmetic.RationalDifferent.log_rootDiscr_eq_log_abs_discr_div_finrank. -/
import tmp.sheaf.xif.paper.Mzk1ULR0BarAdapterActual
import tmp.sheaf.xif.paper.Mzk1G1LocalHeightCriterionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
open scoped Classical
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0D1WiringActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULR0BarDiscActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.G1LocalHeightCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0BarAdapterActual

variable (K : Type) [Field K] [NumberField K]

/-- D1 discOver 是 Def1.9 归一的 log|disc|，与 D = logDifferentF 相同。 -/
theorem discOver_eq_D : discOver K = D K := by
  unfold discOver D logDifferentF
  rw [← IUT.ABCBridge.Arithmetic.RationalDifferent.log_absNorm_differentIdeal_div_finrank_eq_log_rootDiscr K]
  rw [NumberField.absNorm_differentIdeal K (𝓞 K)]

/-- h 槽: D1 的 height consumer 用 hBar（= logHeight₁/[K:Q]）。 -/
theorem hBar_wiring (x : K) :
    hBar K x = Height.logHeight₁ x / (Module.finrank ℚ K : Real) :=
  hBar_adapter K x

/-- truncConductor 是 1/[K:Q] 归一的（定义展开，与 :29-37 的定义逐字一致）。 -/
theorem truncConductor_def_wiring (lam : K) :
    truncConductor lam =
      (∑ᶠ v : NumberField.FinitePlace K,
        if IsBadPlace lam v then
          Real.log (max 1 ((Ideal.absNorm
            (NumberField.FinitePlace.maximalIdeal v).asIdeal : ℕ) : Real))
        else 0) /
        (Module.finrank ℚ K : Real) := rfl

#print axioms discOver_eq_D
#print axioms hBar_wiring
#print axioms truncConductor_def_wiring

end LeanFormal.IUT.XiFPaper.Mzk1ULR0D1WiringActual
