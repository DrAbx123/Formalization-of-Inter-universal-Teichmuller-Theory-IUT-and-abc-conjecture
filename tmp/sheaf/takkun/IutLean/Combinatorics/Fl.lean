import Mathlib

/-!
# 組合せ的 Teichmüller 理論の核: `F_l` とカスプのラベル

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§13, §17, §18 /
[IUT-I] §4 (Multiplicative Combinatorial Teichmüller Theory), §6 (Additive …).

初期 Θ データの素数 `l`(`l ≥ 5` 素数)に対し、`F_l = ℤ/lℤ` 上の組合せ構造を扱う。
テータ関数の代入点のラベルは `F_l` の元で管理され、その対称性が Hodge 劇場の
加法的(幾何学的)/乗法的(数論的)な二つの側面を生む。

* `Fl l = ℤ/lℤ`,  `lStar l = (l-1)/2 = l⋆`,
* `Fl = {-l⋆, …, 0, …, l⋆}` ゆえ `|Fl| = 2·l⋆ + 1 = l`,
* 加法的ラベル `LabCusp±_K ≅ Fl`(位数 `l`),
* 乗法的ラベル `LabCusp_K ≅ Fl⋆ = (Fl∖{0})/{±1}`(位数 `l⋆`),
* 幾何学的対称性 `F_l^{⋊±} = Fl ⋊ {±1} ≅ Gal(X_K/C_K) = Aut_K(X_K)`(位数 `2l`,
  二面体群 `DihedralGroup l`)。

本ファイルの命題はすべて Mathlib のみで **`sorry` 無しに証明**できる。
-/

namespace IUT

/-- 環 `F_l = ℤ/lℤ`。IUT では `l` は `l ≥ 5` の素数。 -/
abbrev Fl (l : ℕ) := ZMod l

/-- `l⋆ = (l-1)/2`。乗法的カスプラベル `LabCusp` の個数であり、また自然な同一視
`Fl = {-l⋆, …, 0, …, l⋆}` における「半径」。 -/
def lStar (l : ℕ) : ℕ := (l - 1) / 2

section Prime

variable (l : ℕ) [Fact l.Prime]

instance : NeZero l := ⟨(Fact.out : Nat.Prime l).pos.ne'⟩

/-- `F_l` は体(`l` が素数なので)。 -/
example : Field (Fl l) := inferInstance

/-- `|F_l| = l`。 -/
theorem card_Fl : Fintype.card (Fl l) = l := ZMod.card l

end Prime

section Odd

variable (l : ℕ)

/-- `l` が奇数なら `2·l⋆ + 1 = l`、すなわち `Fl = {-l⋆,…,0,…,l⋆}` の元数勘定
`|Fl| = 2·l⋆ + 1`。 -/
theorem two_mul_lStar_add_one (hodd : Odd l) : 2 * lStar l + 1 = l := by
  obtain ⟨k, rfl⟩ := hodd
  unfold lStar
  omega

/-- 奇数 `l` に対し `Fl∖{0}` の元数は `2·l⋆`。 -/
theorem card_compl_zero (hodd : Odd l) [Fact l.Prime] :
    Fintype.card {x : Fl l // x ≠ 0} = 2 * lStar l := by
  have hcompl : Fintype.card {x : Fl l // x ≠ 0}
      = Fintype.card (Fl l) - Fintype.card {x : Fl l // x = 0} :=
    Fintype.card_subtype_compl (fun x : Fl l => x = 0)
  rw [Fintype.card_subtype_eq, card_Fl] at hcompl
  have := two_mul_lStar_add_one l hodd
  omega

end Odd

section Negation

variable (l : ℕ) [Fact l.Prime]

/-- 奇素数 `l` に対し `(2 : F_l) ≠ 0`。 -/
theorem two_ne_zero_Fl (hl5 : 5 ≤ l) : (2 : Fl l) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod l) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod l) l]
    intro hdvd
    have hle : l ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  simpa using h

/-- **零カスプの一意性 (Hoshi §17)**。負化作用 `x ↦ -x` の不動点は `0` のみ。
これは零カスプが `{±1}` 対称性の唯一の固定ラベルであることに対応する。 -/
theorem neg_eq_self_iff (hl5 : 5 ≤ l) (x : Fl l) : -x = x ↔ x = 0 := by
  constructor
  · intro h
    have hxx : x + x = 0 := add_eq_zero_iff_eq_neg.mpr h.symm
    have h2x : (2 : Fl l) * x = 0 := by rw [two_mul]; exact hxx
    rcases mul_eq_zero.mp h2x with h0 | h0
    · exact absurd h0 (two_ne_zero_Fl l hl5)
    · exact h0
  · rintro rfl; simp

end Negation

section Symmetry

variable (l : ℕ) [Fact l.Prime]

/-- **幾何学的(加法的)対称性群** `F_l^{⋊±} = F_l ⋊ {±1}`。
[IUT-I] §6 / Hoshi §17 では `Gal(X_K/C_K) = Aut_K(X_K) ≅ F_l ⋊ {±1}`。
位数 `2l` のこの群を二面体群 `DihedralGroup l` でモデル化する
(`x ↦ ±x + a` という `F_l` 上のアフィン変換のなす群と同型)。 -/
abbrev GeoSym (l : ℕ) := DihedralGroup l

/-- `|F_l^{⋊±}| = 2l` (Hoshi §17)。 -/
theorem card_GeoSym : Fintype.card (GeoSym l) = 2 * l := DihedralGroup.card

end Symmetry

section Labels

variable (l : ℕ) [Fact l.Prime]

/-- **加法的カスプラベル** `LabCusp±_K ≅ F_l`(被覆 `X_K → X_K` のカスプ集合, Hoshi §17)。
幾何学的対称性 `F_l^{⋊±}` が作用する。位数は `l`。 -/
abbrev LabCuspPM (l : ℕ) := Fl l

/-- `|LabCusp±_K| = l`。 -/
theorem card_LabCuspPM : Fintype.card (LabCuspPM l) = l := card_Fl l

end Labels

section MultiplicativeLabels

variable (l : ℕ) [Fact l.Prime]

/-- 乗法群 `F_l^×` の中の位数 2 の部分群 `{±1}`(`-1` で生成される)。 -/
def negSubgroup : Subgroup (ZMod l)ˣ := Subgroup.zpowers (-1)

/-- `-1 ∈ F_l^×` の位数は `2`(`l` が奇素数なので `-1 ≠ 1`)。 -/
theorem orderOf_neg_one_units (hl5 : 5 ≤ l) :
    orderOf (-1 : (ZMod l)ˣ) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : (-1 : (ZMod l)ˣ) ≠ 1 := by
    intro h
    rw [Units.ext_iff] at h
    simp only [Units.val_neg, Units.val_one] at h
    have h2 : (2 : ZMod l) = 0 := by linear_combination -h
    exact two_ne_zero_Fl l hl5 h2
  have hsq : (-1 : (ZMod l)ˣ) ^ 2 = 1 := neg_one_sq
  exact orderOf_eq_prime hsq hne

/-- **乗法的カスプラベル** `LabCusp_K ≅ F_l^×/{±1} = F_l⋆`(Hoshi §18)。
テータ関数の非単数的特殊値のラベル集合であり、乗法的/数論的対称性 `F_l⋆` が作用する。 -/
abbrev LabCusp (l : ℕ) [Fact l.Prime] := (ZMod l)ˣ ⧸ negSubgroup l

/-- **`|LabCusp_K| = l⋆ = (l-1)/2`** (Hoshi §18)。
`F_l^×`(位数 `l-1`)を位数 2 の `{±1}` で割った商。Lagrange の定理による。 -/
theorem card_LabCusp (hl5 : 5 ≤ l) : Nat.card (LabCusp l) = lStar l := by
  change Nat.card ((ZMod l)ˣ ⧸ negSubgroup l) = lStar l
  have hlag : Nat.card (ZMod l)ˣ
      = Nat.card ((ZMod l)ˣ ⧸ negSubgroup l) * Nat.card (negSubgroup l) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (negSubgroup l)
  have hG : Nat.card (ZMod l)ˣ = l - 1 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card_units l
  have hH : Nat.card (negSubgroup l) = 2 := by
    rw [negSubgroup, Nat.card_zpowers]; exact orderOf_neg_one_units l hl5
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two (by omega)
  have hstar : 2 * lStar l + 1 = l := two_mul_lStar_add_one l hodd
  rw [hG, hH] at hlag
  omega

end MultiplicativeLabels

end IUT
