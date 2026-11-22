import Mathlib

/-!
# フロベニオイド (Frobenioids) — 単数モノイドの塔と数論的次数

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§2, §6, §27 / [FrdI], [FrdII], [IUT-I] §3。

フロベニオイドは数論的直線束のなす圏を抽象化したものである。その局所的な核は、
非アルキメデス素点 `v` での乗法モノイドの塔
  `O×_v ⊆ O▷_v`  (`O▷_v = {a : 0 < |a| ≤ 1}`, `O×_v = O▷_v` の単数 = 単数群)
であり、商 `O▷_v / O×_v`(= 値モノイド)が**数論的直線束の次数**を測る。
さらに、円分物に対応する捩れ(1 の巾根 μ)を除いた `O×µ_v = O×_v / μ`(Hoshi §10, §27)が、
対数殻(Phase 7)や単テータ環境(Phase 5)に現れる「値群的」単数である。

本ファイルでは、この単数モノイドの塔と完全列、及び数論的次数を Mathlib のモノイド論
(`Associates`, `CommGroup.torsion`)の上で `sorry` 無しに構成する。
-/

namespace IUT.Frobenioid

universe u

/-- **局所フロベニオイド・モノイド** `O▷`([FrdI], Hoshi §6)。
`O▷_v = {a : 0 < |a| ≤ 1}` をモデル化した可換モノイド。 -/
structure LocalMonoid where
  /-- 台となる乗法モノイド `O▷`。 -/
  Otri : Type u
  [commMonoid : CommMonoid Otri]

attribute [instance] LocalMonoid.commMonoid

namespace LocalMonoid

variable (M : LocalMonoid)

/-- **単数群** `O×_v = (O▷)ˣ`。 -/
abbrev unitGroup := (M.Otri)ˣ

/-- **値モノイド** `O▷/O× = Associates O▷`。数論的直線束の次数を測る。 -/
abbrev valueMonoid := Associates M.Otri

/-- **値写像** `O▷ ↠ O▷/O×`(`a ↦ [a]`)。 -/
def valueMap (a : M.Otri) : M.valueMonoid := Associates.mk a

@[simp] theorem valueMap_one : M.valueMap 1 = 1 := Associates.mk_one

/-- 値写像は乗法的: `val(a·b) = val(a)·val(b)`。 -/
theorem valueMap_mul (a b : M.Otri) :
    M.valueMap (a * b) = M.valueMap a * M.valueMap b :=
  Associates.mk_mul_mk.symm

/-- **完全列の中心的事実**: `a` の値が自明 ⟺ `a` は単数。
すなわち `O× = ker(O▷ ↠ O▷/O×)`、完全列 `1 → O× → O▷ → O▷/O× → 1`。 -/
theorem value_trivial_iff_unit (a : M.Otri) : M.valueMap a = 1 ↔ IsUnit a :=
  Associates.mk_eq_one

/-- **`O×µ`** = 単数群を 1 の巾根(捩れ部分群 μ)で割った商(Hoshi §10, §27 の `O×µ_v`)。
円分物に対応する捩れを除いた「値群的」単数。対数殻・単テータ環境に現れる。 -/
abbrev unitsModRoots := M.unitGroup ⧸ CommGroup.torsion M.unitGroup

end LocalMonoid

/-- **フロベニオイド**(の局所的核 = `Model`, [FrdI])。局所モノイド `O▷` に、その値モノイド
`O▷/O×` 上の**数論的次数** `deg`(テンソル積=値の積を実数の和へ送る準同型)を付与したもの。 -/
structure Model where
  /-- 下部の局所モノイド `O▷`。 -/
  base : LocalMonoid
  /-- 数論的次数 `deg : O▷/O× → (ℝ, +)`(乗法的値モノイドから加法的実数へ)。 -/
  deg : base.valueMonoid →* Multiplicative ℝ

namespace Model

variable (F : Model)

/-- 数論的直線束(値モノイドの元)の**次数**(実数値)。 -/
def degree (x : F.base.valueMonoid) : ℝ := Multiplicative.toAdd (F.deg x)

/-- **次数の加法性**: テンソル積(= 値の積)の次数は次数の和。 -/
theorem degree_mul (x y : F.base.valueMonoid) :
    F.degree (x * y) = F.degree x + F.degree y := by
  simp only [degree, map_mul, toAdd_mul]

@[simp] theorem degree_one : F.degree 1 = 0 := by
  simp [degree]

/-- **単数の次数は 0**: 単数 `a` の定める数論的直線束の次数は 0(値が自明だから)。
これは「単数部分は次数に寄与しない」という数論的直線束の基本性質。 -/
theorem degree_valueMap_unit (a : F.base.Otri) (ha : IsUnit a) :
    F.degree (F.base.valueMap a) = 0 := by
  rw [(F.base.value_trivial_iff_unit a).mpr ha, degree_one]

end Model

end IUT.Frobenioid
