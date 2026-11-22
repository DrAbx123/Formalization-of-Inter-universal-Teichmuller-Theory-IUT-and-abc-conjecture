import Mathlib

/-!
# 遠アーベル幾何の基盤: 算術的基本群の完全列 `1 → Δ → Π → G → 1`

底本: [IUT-I] Def 3.1 (b), Hoshi §1–§3, §5。

双曲的曲線 `X_F` に対し、エタール基本群は自然な完全列
`1 → Δ_X → Π_{X_F} → G_F → 1`
を持つ(`Δ_X` = 幾何学的基本群 `π₁(X_F ×_F F̄)`, `Π_{X_F}` = 算術的基本群 `π₁(X_F)`,
`G_F = Gal(F̄/F)`)。遠アーベル幾何では、この群論的データのみから幾何学的対象を復元する。

ここでは(プロ有限位相は後続フェーズに譲り)この完全列の**群論的骨格**を Mathlib の
`GroupExtension` の上に抽象化し、IUT で用いる基本的事実 ―― 完全性、Galois 商 `Π/Δ ≃ G`、
共役による外 Galois 作用 `Π → Aut(Δ)` ―― を整備する。

注: Lean では `Π` は予約語(Pi 型)のため、算術的基本群を表す型変数は `P` と書く。
-/

namespace IUT.Anabelian

universe u

variable {Δ P G : Type u} [Group Δ] [Group P] [Group G]

/-- **算術的基本群の完全列** `1 → Δ → P → G → 1`(数学的記号では `1 → Δ → Π → G → 1`)。
`Δ` = 幾何学的基本群、`P`(= Π)= 算術的基本群、`G` = 絶対 Galois 群。
Mathlib の `GroupExtension`(分裂とは限らない群拡大)として実装する。 -/
abbrev ArithFundSeq (Δ P G : Type u) [Group Δ] [Group P] [Group G] :=
  GroupExtension Δ P G

namespace ArithFundSeq

variable (S : ArithFundSeq Δ P G)

/-- 幾何学的部分 `Δ ↪ Π` は単射。 -/
theorem geom_injective : Function.Injective S.inl := S.inl_injective

/-- 射影 `Π ↠ G` は全射。 -/
theorem galois_surjective : Function.Surjective S.rightHom := S.rightHom_surjective

/-- **完全性**(`Π` の所): `Δ` の像 = `G` への射の核。 -/
theorem exact_middle : S.inl.range = S.rightHom.ker :=
  S.range_inl_eq_ker_rightHom

/-- 幾何学的元は Galois へ自明に写る(`G_F` への作用が幾何学的部分で消える)。 -/
@[simp] theorem galois_of_geom (d : Δ) : S.rightHom (S.inl d) = 1 :=
  S.rightHom_inl d

/-- **Galois 商** `Π ⧸ Δ ≃* G`。算術的基本群を幾何学的基本群で割ると絶対 Galois 群。 -/
noncomputable def galoisQuotient : P ⧸ S.inl.range ≃* G :=
  S.quotientRangeInlEquivRight

/-- **外 Galois 作用(上部)** `Π → Aut(Δ)`: 算術的基本群が幾何学的基本群に共役で作用する。
これを内部自己同型で割ったものが、遠アーベル幾何の核心 `G_F → Out(Δ_X)` を与える。 -/
noncomputable def outerActionUp : P →* MulAut Δ :=
  S.conjAct

/-- 共役作用と包含の両立性: `inl (conjAct π d) = π · inl d · π⁻¹`。 -/
theorem geom_conj (p : P) (d : Δ) :
    S.inl (S.outerActionUp p d) = p * S.inl d * p⁻¹ :=
  S.inl_conjAct_comm

end ArithFundSeq

end IUT.Anabelian
