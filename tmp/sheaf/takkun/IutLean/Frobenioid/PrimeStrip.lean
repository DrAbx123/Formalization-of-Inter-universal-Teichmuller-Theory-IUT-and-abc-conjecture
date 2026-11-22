import Mathlib
import tmp.sheaf.takkun.IutLean.Frobenioid.Basic

/-!
# 素点縞 (Prime strips) と大域的数論的次数 (Track F)

底本: [IUT-I] §3–§6, 星裕一郎入門 §6, §8, §27 / [FrdI], [FrdII]。

**素点縞** (prime strip) `𝔉 = {𝔉_v}_{v∈V}` は、各素点 `v ∈ V` に局所フロベニオイド `𝔉_v` を
割り当てる族である。Hodge 劇場はこの素点縞の系を骨格に持つ。

数論的直線束(各素点での値モノイドの元の族)の**大域的次数**は、局所次数の(有限素点上の)
**和** `Σ_v deg_v` で与えられる。本ファイルでは、この大域次数の**加法性**(テンソル積の次数が
次数の和)を `sorry` 無しに証明する ―― これが高さ(q 標対象の次数)計算の代数的骨格である。

これは `HasPrimeStripSystem`(Hodge 劇場の素点縞系)を将来具体化するための Track F の基盤。
-/

namespace IUT.Frobenioid

/-- **素点縞** (prime strip): 各素点 `v ∈ V` に局所フロベニオイド `Model` を割り当てる族。 -/
structure PrimeStrip (V : Type*) where
  /-- 各素点での局所フロベニオイド `𝔉_v`。 -/
  loc : V → Model

namespace PrimeStrip

variable {V : Type*} (𝔉 : PrimeStrip V)

/-- **大域的数論的次数**: 有限素点集合 `s` 上の局所次数の和 `Σ_{v∈s} deg_v(x_v)`。
数論的直線束 `x = {x_v}` の(`s` に台を持つ)大域次数。 -/
def totalDegree (s : Finset V) (x : ∀ v, (𝔉.loc v).base.valueMonoid) : ℝ :=
  ∑ v ∈ s, (𝔉.loc v).degree (x v)

/-- **大域次数の加法性**: テンソル積(局所的に積)の大域次数は、各々の大域次数の和。
`deg(x ⊗ y) = deg(x) + deg(y)`。高さ計算の基礎(積=和の対応)。 -/
theorem totalDegree_mul (s : Finset V) (x y : ∀ v, (𝔉.loc v).base.valueMonoid) :
    𝔉.totalDegree s (fun v => x v * y v)
      = 𝔉.totalDegree s x + 𝔉.totalDegree s y := by
  unfold totalDegree
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => (𝔉.loc v).degree_mul (x v) (y v))

/-- 自明な数論的直線束の大域次数は `0`。 -/
theorem totalDegree_one (s : Finset V) :
    𝔉.totalDegree s (fun _ => 1) = 0 := by
  simp [totalDegree, Model.degree_one]

end PrimeStrip

/-- 素点縞は非空(各素点に自明フロベニオイド `O▷ = ℕ` を置く具体例)。 -/
def trivialStrip (V : Type*) : PrimeStrip V where
  loc := fun _ => { base := { Otri := ℕ }, deg := 1 }

end IUT.Frobenioid
