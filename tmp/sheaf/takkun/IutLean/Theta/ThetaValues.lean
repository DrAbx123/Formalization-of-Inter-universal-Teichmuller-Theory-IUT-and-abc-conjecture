import Mathlib
import tmp.sheaf.takkun.IutLean.Combinatorics.Fl

/-!
# テータ関数の特殊値 — Gauss 分布と `±1` 対称性

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§13, §16, §18, §27 / [EtTh], [IUT-II]。

エタールテータ関数 `Θ̈` の(標準型に正規化した乗法的逆元の)`j` でラベル付けされた代入点
`ξ_j` での特殊値は (Hoshi §13 (m))
`Θ̈std(ξ_j)⁻¹ = ±q_E^{j²/2}`
であり、その `q_E` の肩に乗る整数は **`j ↦ j²` という Gauss 分布的な形**をしている。

この Gauss 分布の `±1` 対称性 `(−j)² = j²` により、テータ関数の非単数的特殊値は
**`LabCusp ≅ F_l^×/{±1}` でラベル付けされる**(Hoshi §18, §27)。本ファイルでは
この特殊値の組合せ的核を `sorry` 無しで証明し、Phase 1 のラベル理論に接続する。
-/

namespace IUT.Theta

/-- **Gauss 分布の指数**: `j` でラベル付けされた標準型テータ値 `±q^{j²/2}` における、
`q` の肩に乗る整数(全体の `1/2` を除いて) `j²`。 -/
def gaussExp (j : ℤ) : ℤ := j ^ 2

@[simp] theorem gaussExp_neg (j : ℤ) : gaussExp (-j) = gaussExp j := by
  unfold gaussExp; ring

@[simp] theorem gaussExp_zero : gaussExp 0 = 0 := by
  unfold gaussExp; ring

theorem gaussExp_nonneg (j : ℤ) : 0 ≤ gaussExp j := by
  unfold gaussExp; positivity

/-- Gauss 分布の階差 `e(j+1) − e(j) = 2j+1`(二次=Gauss 的であることの表現)。 -/
theorem gaussExp_succ_sub (j : ℤ) : gaussExp (j + 1) - gaussExp j = 2 * j + 1 := by
  unfold gaussExp; ring

section Value

variable {M : Type*} [CommGroup M]

/-- **標準型テータ関数の特殊値** `θ(ξ_j) = q^{j²}`(符号・1 の巾根の寄与を除く)。
`q : M` は `q_E`(の適切な巾根)、値は乗法群 `M` の中で `zpow` で表す。
正規化により `θ(ξ_0) = 1`、`θ(ξ_j) = θ(ξ_j)/θ(ξ_0)` は Hoshi §13 (l) の比に対応。 -/
def thetaValue (q : M) (j : ℤ) : M := q ^ gaussExp j

@[simp] theorem thetaValue_zero (q : M) : thetaValue q 0 = 1 := by
  simp [thetaValue]

/-- **テータ値の `±1` 対称性** (Hoshi §18, §27): `θ(ξ_{−j}) = θ(ξ_j)`。
ゆえにテータ関数の非単数的特殊値は `F_l^×/{±1} ≅ LabCusp` でラベル付けされる。 -/
@[simp] theorem thetaValue_neg (q : M) (j : ℤ) :
    thetaValue q (-j) = thetaValue q j := by
  unfold thetaValue; rw [gaussExp_neg]

/-- 値が `±1` 軌道で一定であることの言い換え: `j` と `j'` が `j' = ±j` で関連すれば値は一致。 -/
theorem thetaValue_eq_of_eq_neg (q : M) {j j' : ℤ} (h : j' = j ∨ j' = -j) :
    thetaValue q j' = thetaValue q j := by
  rcases h with h | h <;> subst h <;> simp

/-- テータ値の比 `θ(ξ_j) / θ(ξ_0) = q^{j²}`(Hoshi §13 (l) の `q^{j²/2}` に対応)。 -/
theorem thetaValue_div_zero (q : M) (j : ℤ) :
    thetaValue q j / thetaValue q 0 = q ^ gaussExp j := by
  simp [thetaValue]

end Value

section MonoidValue

variable {M : Type*} [CommMonoid M]

/-- **可換モノイドにおけるテータ値** `θ(ξ_j) = q^{j²}`(`j² ≥ 0` ゆえ自然数巾)。
プライム縞の局所単項式 `O▷`(群とは限らない)に直接適用できる版。 -/
def thetaValueMon (q : M) (j : ℤ) : M := q ^ (gaussExp j).toNat

@[simp] theorem thetaValueMon_zero (q : M) : thetaValueMon q 0 = 1 := by
  simp [thetaValueMon]

/-- **可換モノイド版テータ値の `±1` 対称性** (Hoshi §18, §27): `θ(ξ_{−j}) = θ(ξ_j)`。 -/
@[simp] theorem thetaValueMon_neg (q : M) (j : ℤ) :
    thetaValueMon q (-j) = thetaValueMon q j := by
  unfold thetaValueMon; rw [gaussExp_neg]

end MonoidValue

end IUT.Theta
