/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # A1032: concrete thetaData assembly skeleton (GAP-CONCRETE)

| field | value |
|---|---|
| Status | SKELETON / GAP-CONCRETE: imports not yet ported; no theorem claimed |
| 来源 | `Iut/Concrete/Existence.lean:303 thetaData`; `Iut/Tripod/Providers.lean:34 tripodProviders`; `Iut/Tripod/CurveFacts.lean:369 CurveProviders`, `:385 curve`, `:389 tate`, `:377 modRep`, `:443 sl2Image` |
| 依赖 | `Iut.Tripod.Providers`（tripodProviders）、`Iut.Concrete.Existence`、`Iut.Cor312.ThetaData.Basic`（InitialThetaData）；这些 lana root oelan 尚未 port/build |
| GAP | 具体 `x : Pt`、`hP2`、`hP4`、`hP5`、`hcore`、`hsl` 是显式假设；ℓ=5 被 thetaData 的 `h7 : 7 ≤ ℓ` 排除；`tripodProviders` 的 Tripod 闭包未 port |
| 说明 | 下面的 Lean 代码放在注释块中，等 mainline port 出 `Iut.Tripod.Providers` / `Iut.Concrete.Existence` 后取消注释并适配 import；当前文件只含 Mathlib，不伪造任何对象/定理。 |
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConcreteThetaDataActual

/-- Status marker for downstream bookkeeping (no mathematical content). -/
def status : String := "GAP-CONCRETE: tripodProviders/Existence not yet ported"

/-
PLANNED CODE (uncomment after porting `Iut.Tripod.Providers` and
`Iut.Concrete.Existence`, adapting imports and universes):

import Iut.Tripod.Providers
import Iut.Concrete.Existence
import Iut.Cor312.ThetaData.Basic

open Iut
open Iut.Tripod
open Matrix

variable (P : CurveProviders) (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ),
    A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
  (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll),
    ¬ ℓ ∣ (P.tate x).qOrder w hw)
  (hP5 : ∃ w ∈ (P.curve x).badAll,
    residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
  (hcore : OrbicurveDataSection.HasCoreUniversally (P.curve x).F (P.curve x).E)

/-- Concrete `InitialThetaData` from the Tripod providers and explicit source
hypotheses.  `hsl` is supplied explicitly; it can be discharged from
`CurveFacts.sl2Image` once the `localData`-vs-`badAll` bridge is available. -/
noncomputable def concreteThetaData : InitialThetaData :=
  thetaData (P.curve x) (P.arith x) (P.tate x) hℓ h7
    (P.modRep x ℓ hℓ) hsl hP2 hP5 hcore
-/

end LeanFormal.IUT.XiFPaper.Mzk1ConcreteThetaDataActual
