import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

lemma omega_step_algebra {a b c d e f g B E F : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hg : g ≠ 0)
    (hf : f * g = b ^ 2 * a * F - c * a * E ^ 2)
    (hd : d * g = c ^ 2 * b * E - B * b * a ^ 2)
    (he : e = E * b ^ 3 - c * a ^ 3)
    (hrel : b ^ 2 * c * F - a ^ 2 * B * E = g ^ 2 * e) :
    f / a ^ 4 = - (d / b ^ 4) + (g - d / b ^ 4) * (e / (a ^ 3 * c)) := by
  have hE0 : f * b ^ 4 * c + d * a ^ 4 * c - g * e * a * b ^ 4 + d * e * a = 0 := by
    have h1 : (f * b ^ 4 * c + d * a ^ 4 * c - g * e * a * b ^ 4 + d * e * a) * g = 0 := by
      linear_combination (norm := ring) (b ^ 4 * c) * hf + (a ^ 4 * c + e * a) * hd +
        (a * b ^ 4) * hrel - (a * b * (B * a ^ 2 - E * c ^ 2)) * he
    exact (mul_eq_zero.mp h1).resolve_right hg
  field_simp [ha, hb, hc, hg]
  linear_combination hE0

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
