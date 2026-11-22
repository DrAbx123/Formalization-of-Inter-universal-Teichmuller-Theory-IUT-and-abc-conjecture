/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.takkun.IutLean.Diophantine.Thm110

/-! # A511 glue: explicit-constant objects from the Takkun Thm 1.10 elementary deduction -/

noncomputable section

namespace LeanFormal.IUT.Objects.ExplicitConstants

open IUT.Diophantine

/-- The explicit constant data of the elementary Thm 1.10 stage: the real parameters of the
paper's final elementary deduction together with its proven inequality. -/
structure ExplicitConstantObject where
  /-- The prime `l ≥ 7`. -/
  l : ℝ
  /-- The modified degree `d_mod`. -/
  dmod : ℝ
  /-- The `e*` parameter. -/
  estar : ℝ
  /-- The `η` parameter. -/
  eta : ℝ
  /-- The log of the q-pilot value. -/
  logq : ℝ
  /-- The `D` constant. -/
  D : ℝ
  hl : 7 ≤ l
  hq : 0 ≤ logq
  hD : 0 ≤ D
  hdmod : 1 ≤ dmod
  hestar : 1 ≤ estar
  heta : 0 ≤ eta
  /-- The Thm 1.10 elementary stage input inequality. -/
  input_bound :
    1/6 * (1 - 12/l^2) * logq ≤ (1 + 12*dmod/l) * D + 10*(estar*l + eta)
  /-- The proven output inequality (the object's explicit-constant content). -/
  output_bound :
    1/6 * logq ≤ (1 + 20*dmod/l) * D + 20*(estar*l + eta)

/-- Build the explicit-constant object; `output_bound` is derived by the ported Takkun
theorem `thm110_elementary_deduction` (real proof, no gap assumed). -/
def explicitConstantObjectOf (l dmod estar eta logq D : ℝ)
    (hl : 7 ≤ l) (hq : 0 ≤ logq) (hD : 0 ≤ D)
    (hdmod : 1 ≤ dmod) (hestar : 1 ≤ estar) (heta : 0 ≤ eta)
    (h312 : 1/6 * (1 - 12/l^2) * logq ≤ (1 + 12*dmod/l) * D + 10*(estar*l + eta)) :
    ExplicitConstantObject where
  l := l
  dmod := dmod
  estar := estar
  eta := eta
  logq := logq
  D := D
  hl := hl
  hq := hq
  hD := hD
  hdmod := hdmod
  hestar := hestar
  heta := heta
  input_bound := h312
  output_bound := thm110_elementary_deduction l dmod estar eta logq D hl hq hD hdmod hestar heta h312

end LeanFormal.IUT.Objects.ExplicitConstants
