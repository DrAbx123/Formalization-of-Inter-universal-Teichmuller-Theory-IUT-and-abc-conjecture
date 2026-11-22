import Mathlib

/-!
# 円分物 (Cyclotomes) — IUT の遠アーベル幾何の最初の素材

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§1「円分物」, §2「フロベニオイドの円分剛性同型」。

## 背景 (Hoshi §1)

数論幾何には様々な姿の **Tate 捻り** `Ẑ(1)` が現れる:
* `(a)` 代数閉体 `Ω` に対する `Λ(Ω) = lim μ_n(Ω)`,
* `(b)` 射影的滑らかな曲線 `C` に対する `Hom(H²ét(C,Ẑ), Ẑ)`,
* `(c)` 閉点 `c ∈ C` の惰性群 `I_c`.

スキーム論(=環論的枠組み)では、これらの間に**標準的同型**が環構造から自然に定まる。
しかし遠アーベル幾何(=群論的枠組み)では、円分物の間の同一視は**直ちには存在せず**、
その標準的同型の存在は非自明な定理 ―― **円分同期化同型 / 円分剛性同型**
(cyclotomic synchronization / rigidity isomorphism) ―― となる。

本ファイルでは、円分物そのものを「基底環 `R`(道徳的には `R = Ẑ`)上の階数 1 の自由加群」
として抽象化する。`R`-線型同型の言葉で、

* **非標準的な比較同型の存在**(任意の 2 つの円分物は抽象的には同型) ―― ここで完全証明、
* **標準的(剛性)同型**(群論的設定から関手的に定まるもの) ―― 深い定理として将来目標、

を区別する。これは Hoshi §1 の論理構造そのものである。
-/

namespace IUT

universe u v w

variable (R : Type u) [CommRing R]

/-- **円分物** (cyclotome)。基底環 `R`(道徳的には `R = Ẑ`)上の加群 `M` が円分物であるとは、
`M` が `R` 上階数 1 の自由加群であること、すなわち `R`-線型同型 `M ≃ₗ[R] R` が存在することをいう。

これは Tate 捻り `Ẑ(1)` の様々な姿 (Hoshi §1 の (a),(b),(c)) の共通の抽象である。 -/
def IsCyclotome (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Nonempty (M ≃ₗ[R] R)

namespace IsCyclotome

variable {R}
variable {M : Type v} {N : Type w}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 円分物 `M` の標準基底による `R` との(一つの)同型を取り出す。
`R = Ẑ` のときこれは `M` の「位相的生成元の選択」に対応し、**標準的ではない**ことに注意。 -/
noncomputable def equivBase (h : IsCyclotome R M) : M ≃ₗ[R] R :=
  Nonempty.some h

/-- 基底環 `R` 自身は自明に円分物である(恒等同型)。 -/
theorem self : IsCyclotome R R :=
  ⟨LinearEquiv.refl R R⟩

/-- **円分比較同型の(非標準的)存在** (Hoshi §1)。
任意の 2 つの円分物 `M`, `N` の間には `R`-線型同型が存在する。

これは「群論的枠組みでも、円分物が**抽象的には**同型である」という、円分剛性の議論の出発点。
ただしここで得られる同型は**標準的ではない**(基底の選び方に依存する)。標準的同型を
群論的設定から関手的に取り出すことこそが円分剛性同型の内容であり、別途の定理となる
([cf. 将来の Phase 3]: `H ⊆ G ↠ Q` からの純群論的構成)。 -/
theorem comparison (hM : IsCyclotome R M) (hN : IsCyclotome R N) :
    Nonempty (M ≃ₗ[R] N) :=
  ⟨(equivBase hM).trans (equivBase hN).symm⟩

/-- 円分物上の `R`-線型自己同型は、`R` のある単元による乗法と一致する。
`R = Ẑ` のとき自己同型群は `Ẑ^× = ∏ ℤ_p^×` であり、円分指標の値域に対応する。
(ここでは自己同型を `R` の自己同型へ移送する形で抽象的に述べる。) -/
noncomputable def autEquivBaseAut (h : IsCyclotome R M) :
    (M ≃ₗ[R] M) ≃ (R ≃ₗ[R] R) where
  toFun φ := (equivBase h).symm.trans (φ.trans (equivBase h))
  invFun ψ := (equivBase h).trans (ψ.trans (equivBase h).symm)
  left_inv φ := by ext x; simp
  right_inv ψ := by ext x; simp

end IsCyclotome

end IUT
