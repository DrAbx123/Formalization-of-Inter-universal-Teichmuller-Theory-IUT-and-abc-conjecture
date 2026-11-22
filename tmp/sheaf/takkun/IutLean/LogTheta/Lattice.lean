import Mathlib
import tmp.sheaf.takkun.IutLean.HodgeTheater.Defs

/-!
# log-theta-lattice (対数テータ格子)

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§9, §26 / [IUT-III]。

**log-theta-lattice** は、`ℤ × ℤ` で添字付けられた Θ±ellNF Hodge 劇場 (`Full`) の格子であり、
* **縦方向**(`(n,m) → (n,m+1)`)は**対数リンク** (log-link) で、
* **横方向**(`(n,m) → (n+1,m)`)は**Θ リンク** (Θ-link) で
結ばれる。本質的に重要な点は、この 2 種類のリンクが**可換でない**ことである
(対数リンクは正則(環)構造に依存するが、Θ リンクは依存しない)。
-/

namespace IUT.LogTheta

open IUT.HodgeTheater

/-- **log-theta-lattice**: `ℤ × ℤ` 上の Θ±ellNF Hodge 劇場の格子。
第 1 成分が Θ リンク方向(横)、第 2 成分が対数リンク方向(縦)。 -/
structure LogThetaLattice where
  /-- 格子点 `(n, m) ∈ ℤ × ℤ` に置かれた Θ±ellNF Hodge 劇場。 -/
  HT : ℤ × ℤ → Full

namespace LogThetaLattice

variable (L : LogThetaLattice)

/-- 第 `n` **Θ 列** (Θ-column): Θ リンク位置 `n` を固定し、対数リンクで縦に並ぶ Hodge 劇場の列。
対数 Kummer 対応 (Hoshi §9, §10) はこの列に沿って考えられる。 -/
def thetaColumn (n : ℤ) : ℤ → Full := fun m => L.HT (n, m)

/-- 第 `m` **対数行** (log-row): 対数リンク位置 `m` を固定し、Θ リンクで横に並ぶ Hodge 劇場の列。 -/
def logRow (m : ℤ) : ℤ → Full := fun n => L.HT (n, m)

@[simp] theorem thetaColumn_apply (n m : ℤ) : L.thetaColumn n m = L.HT (n, m) := rfl

@[simp] theorem logRow_apply (n m : ℤ) : L.logRow m n = L.HT (n, m) := rfl

end LogThetaLattice

end IUT.LogTheta
