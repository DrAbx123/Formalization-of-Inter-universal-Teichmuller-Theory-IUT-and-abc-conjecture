/- Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Algebra.Rat

/-!
# モジュライ体 `F_mod = ℚ(j_E)` (Track B / [IUT-I] Def 3.1(b))

底本: [IUT-I] Definition 3.1 (b)(`F_mod` は `X_F` のモジュライ体, `F_mod = ℚ(j_E)`)。

楕円曲線 `E` のモジュライ体は、その `j` 不変量で生成される `ℚ` の拡大 `ℚ(j_E)` である。
本ファイルでは、Mathlib の `WeierstrassCurve.j` と `IntermediateField` の単純拡大を用いて
`F_mod = ℚ(j_E)` を構成し、その基本性質(`j ∈ F_mod`、`F_mod` は `j` を含む最小の部分体)を
`sorry` 無しに証明する。さらに条件 (b) の `GaloisOverFieldOfModuli`(`F/F_mod` が `l` と素な
次数の Galois 拡大)を**具体的命題**として与える(Track B)。

A504: `import Mathlib` を必要最小限のモジュールに分割(全 Mathlib 取込による OOM 回避)。
-/

namespace IUT.EllipticCurve

open WeierstrassCurve IntermediateField

variable {F : Type*} [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- 楕円曲線の**モジュライ体** `F_mod = ℚ(j_E)`(`j` 不変量で生成される `F` の部分体)。 -/
def fieldOfModuli : IntermediateField ℚ F := ℚ⟮W.j⟯

/-- `j` 不変量はモジュライ体に属する。 -/
theorem j_mem_fieldOfModuli : W.j ∈ fieldOfModuli W :=
  mem_adjoin_simple_self ℚ W.j

/-- モジュライ体は `j` を含む最小の部分体: `j ∈ E ⟹ F_mod ≤ E`。 -/
theorem fieldOfModuli_le {E : IntermediateField ℚ F} (h : W.j ∈ E) :
    fieldOfModuli W ≤ E := by
  rw [fieldOfModuli, adjoin_simple_le_iff]
  exact h

/-- **[IUT-I] Def 3.1(b) の `GaloisOverFieldOfModuli` の具体化**(Track B): `F/F_mod` が
`l` と素な次数の Galois 拡大(`F_mod = ℚ(j_E)`)。旧 `opaque IUT.GaloisOverFieldOfModuli` を
この**具体的命題**に置き換える。 -/
def GaloisOverFieldOfModuli (l : ℕ) : Prop :=
  IsGalois (fieldOfModuli W) F ∧ (Module.finrank (fieldOfModuli W) F).Coprime l

end IUT.EllipticCurve
