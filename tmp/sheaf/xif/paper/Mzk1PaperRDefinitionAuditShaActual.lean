import tmp.sheaf.xif.paper.S709RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.Mzk1RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullScalingShaActual
import Mathlib.Tactic

/-!
# A805 paper-side `r` definition check (shehdd)

Paper/lana r: at a finite place, `I_w <= p^{-r_w} O_w` sharply with the log-shell radius
`r_w = logShellRadius`; lana defines it as `sSup ((fun y => -ordp K w y) '' (logShell ...))`
(`Iut/WallEquiv/VcI.lean:463`), achieved at the maximizing element (:468, :471).

On our completed root side the theta-hull radius is
`rootImageRadius_b = p_b^{-c_norm_b/(2ℓ)}` (S709 / A762), so the corresponding paper `r` is

  `paperR_b := c_norm_b / (2ℓ)`, and `rootImageRadius_b = p_b^{-paperR_b}`.

Proved here:
* `rootImageRadius_eq_rpow_neg_paperR`;
* `log_rootImageRadius_eq_neg_paperR_mul_logp`;
* capsule exponent dictionary `capsuleDivisorExponent T b j = paperR_b * j^2`
  (so the A775 capsule scale `qroot^{j²}` has divisor exponent `paperR_b*j²`);
* q-root relation `qroot^{2ℓ} = qUnit` is re-exported from PaperRootCompletionTensorActual.

PENDING (lana olean): the exact equality `paperR_b = logShellRadius` at the finite place
(`VcI.lean:463/468/471`); lana is not compiled here, so it is recorded not asserted.
No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperRDefinitionAuditShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Paper-side normalized `r`: `r_b = c_norm_b / (2ℓ)`. -/
noncomputable def paperR : ℝ :=
  (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b) /
    (2 * (l.value : ℝ))

/-- The diameter-radius dictionary: `rootImageRadius_b = p_b^{-paperR_b}`. -/
theorem rootImageRadius_eq_rpow_neg_paperR :
    (rootImageRadius T b : ℝ) =
      Real.rpow (qVFamTensorP T b : ℝ) (-(paperR T b)) := by
  unfold paperR
  rw [rootImageRadius_eq_p_rpow_reexport]
  congr 1
  ring

/-- Log form: `log(rootImageRadius_b) = -paperR_b * log p_b`. -/
theorem log_rootImageRadius_eq_neg_paperR_mul_logp :
    Real.log (rootImageRadius T b : ℝ) =
      -(paperR T b) * Real.log (qVFamTensorP T b : ℝ) := by
  unfold paperR
  rw [log_rootImageRadius_eq_neg_coeff_mul_logp_div_twoL]
  ring

/-- **Capsule exponent dictionary**: the A775 divisor exponent for capsule `j` is
`paperR_b * j²` (paper scaling `qroot^{j²}`). -/
theorem capsuleDivisorExponent_eq_paperR_mul (j : ℕ) :
    Mzk1ScaledThetaHullScalingShaActual.capsuleDivisorExponent T b j =
      paperR T b * (j : ℝ) ^ 2 := by
  unfold paperR Mzk1ScaledThetaHullScalingShaActual.capsuleDivisorExponent
  ring

structure PaperRRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def paperRRows : List PaperRRow :=
  [ ⟨"paper r definition", "I_w <= p^{-r_w}O_w sharp; r_w = logShellRadius = -ordp (lana VcI.lean:463, :468, :471)", "PENDING (lana olean)"⟩
  , ⟨"our r", "paperR_b = c_norm_b/(2l)", "DEF"⟩
  , ⟨"radius form", "rootImageRadius_b = p_b^{-paperR_b}", "PROVED"⟩
  , ⟨"log form", "log rootImageRadius_b = -paperR_b * log p_b", "PROVED"⟩
  , ⟨"q-root equation", "root^{2l} = qUnit (qroot^{2l}=q_v unit side)", "PROVED (re-export)"⟩
  , ⟨"capsule scale", "capsule divisor exponent = paperR_b * j^2 (j=i+1)", "PROVED"⟩
  , ⟨"lana exact match", "paperR_b = logShellRadius at the finite place", "PENDING (VcI.lean:463/468/471)"⟩
  , ⟨"scope", "paper-side dictionary only; no lana import; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem paperRRows_length : paperRRows.length = 8 := rfl

theorem paperRRows_has_pending :
    paperRRows.any (fun r => r.status = "PENDING (lana olean)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1PaperRDefinitionAuditShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRDefinitionAuditShaActual.rootImageRadius_eq_rpow_neg_paperR
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRDefinitionAuditShaActual.log_rootImageRadius_eq_neg_paperR_mul_logp
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRDefinitionAuditShaActual.capsuleDivisorExponent_eq_paperR_mul
