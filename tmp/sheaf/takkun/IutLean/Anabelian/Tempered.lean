import Mathlib
import tmp.sheaf.takkun.IutLean.Anabelian.FundamentalSequence

/-!
# 緩 (tempered) 基本群 — プロ有限完備化への比較の抽象

底本: [IUT-I] §2 (Complements on Tempered Coverings), 星裕一郎入門 §6。

`p` 進双曲的曲線 `X` に対し、有限エタール被覆と(特殊ファイバーの双対半グラフから来る)
「グラフ論的」無限被覆を組み合わせた**緩被覆 (tempered covering)** を分類する位相群
`π₁^tp(X)`(緩基本群)がある。これはそのプロ有限完備化 `π₁(X)` に自然に**稠密に埋め込まれる**。

ここでは(位相・半グラフ構造は後続に譲り)この比較 `π₁^tp ↪ π₁` の**群論的核** ―― 単射性と
それが与える埋め込み `π₁^tp ≃ Im` ―― を扱う。[IUT-I] §2 の主結果(緩基本群における分解群・
惰性群のプロ有限共役に関する定理)は `TemperedDecompositionConjugacy` として保留する。
-/

namespace IUT.Anabelian

open Pointwise

universe u

/-- **緩–プロ有限比較**: 緩基本群 `T = π₁^tp` からそのプロ有限完備化 `P = π₁` への
比較準同型 `ι`(単射、稠密像)。ここでは代数的核である単射性を記録し、位相的稠密性と
半グラフ構造は保留する。 -/
structure TemperedComparison (T P : Type u) [Group T] [Group P] where
  /-- 緩基本群からプロ有限完備化への比較準同型。 -/
  ι : T →* P
  /-- 比較準同型は単射(緩基本群はそのプロ有限完備化に埋め込まれる)。 -/
  injective : Function.Injective ι

namespace TemperedComparison

variable {T P : Type u} [Group T] [Group P] (c : TemperedComparison T P)

/-- **緩基本群はプロ有限完備化の中の(稠密)部分群と同型**: `π₁^tp ≃* Im(ι) ⊆ π₁`。
これが「緩基本群はプロ有限完備化に埋め込まれる」という主張の群論的内容。 -/
noncomputable def equivRange : T ≃* c.ι.range :=
  MonoidHom.ofInjective c.injective

/-- 埋め込みの像での値は比較準同型の値に一致する。 -/
@[simp] theorem coe_equivRange (t : T) : (c.equivRange t : P) = c.ι t := rfl

/-- 惰性部分群の像はプロ有限完備化の像 `ι(T)` に含まれる(`I ≤ T` ゆえ常に成立、証明済み)。
これは Corollary 2.5 の各「if and only if」の自明な向きの根拠。 -/
theorem inertiaImage_le_range (I : Subgroup T) : I.map c.ι ≤ c.ι.range :=
  Subgroup.map_le_range c.ι I

end TemperedComparison

/-- **[IUT-I] Theorem B / Corollary 2.5 の具体化(脱ブラックボックス化)** ―― 緩分解群・
惰性群のプロ有限共役。

旧 `opaque` を、Corollary 2.5 の**具体的な群論的命題**に置換した。緩基本群 `T = Πᵗᵖ_X` の
惰性部分群族 `inertia`(各カスプに付随)と、プロ有限完備化への単射 `ι : T ↪ P = Π_X` に対し:

* **(a)** `ι(I)` の `P`-共役が `ι(T)` に含まれるなら、それは実は `ι(I)` の `T`-共役である
  (「プロ有限共役 ⟹ 緩共役」、Section Conjecture の極めて弱い版);
* **(b)** `ι(T)` の `P`-共役が `ι(I)` を含むなら、その共役は `ι(T)` 自身に等しい
  (`Πᵗᵖ_X` の commensurable terminality 的剛性)。

これは恒真ではない(Mochizuki の Theorem B そのもの)。証明は Proposition 2.4 ―― 緩被覆の
半グラフのコンパクト性・コア性 ―― を要し、半グラフ理論の形式化後に供給する。自明な逆向き
(`共役が ι(T) に等しい ⟹ ι(I) を含む` 等)は `inertiaImage_le_range` で押さえられている。 -/
def TemperedDecompositionConjugacy {T P : Type u} [Group T] [Group P]
    (c : TemperedComparison T P) (inertia : Set (Subgroup T)) : Prop :=
  ∀ I ∈ inertia,
    (∀ p : P, MulAut.conj p • I.map c.ι ≤ c.ι.range →
        ∃ t : T, MulAut.conj p • I.map c.ι = MulAut.conj (c.ι t) • I.map c.ι) ∧
    (∀ p : P, I.map c.ι ≤ MulAut.conj p • c.ι.range →
        MulAut.conj p • c.ι.range = c.ι.range)

end IUT.Anabelian
