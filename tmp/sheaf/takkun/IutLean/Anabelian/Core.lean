import Mathlib

/-!
# コア性 (`k`-core / coricity) — 終対象としての定式化

底本: [IUT-I] Def 3.1 (d)([CanLift], Rem 2.1.1; [EtTh] §2 冒頭), 星裕一郎入門 §5, §6, §13, §17。

双曲的(軌道)曲線 `X` に対し、「`X` が `k`-core である」とは、`X` を有限エタール被覆/同種で
関連付ける曲線たちのなす圏において `X` が**終対象 (terminal object)** であること、すなわち
Hoshi が §13 で述べる「終対象性」を満たすことである。

この圏論的定式化から、IUT で繰り返し用いられる帰結 ―― **`k`-core の自己同型は恒等のみ**
(Hoshi §17 の `Aut_K(C_K) = {id}`、Phase 1 の対称性計算 `Aut_K(X_K) ≅ F_l ⋊ {±1}` の根拠)
―― が直ちに従う。本ファイルではこれらを Mathlib の圏論(`IsTerminal`)の上で**完全に証明**する。
-/

namespace IUT.Anabelian

open CategoryTheory CategoryTheory.Limits

universe v u

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- **`k`-core**: 曲線 `X` を有限エタール被覆/同種で関連付ける対象のなす圏 `𝒞` において、
`X` が終対象であること(Hoshi §13 の「終対象性」)。 -/
def IsCore (X : 𝒞) : Prop := Nonempty (IsTerminal X)

namespace IsCore

variable {X X' : 𝒞}

/-- コア性の証拠(終対象であること)を取り出す。 -/
noncomputable def isTerminal (h : IsCore X) : IsTerminal X := h.some

/-- **コアへの射の一意性**: 任意の `Y` から `k`-core `X` への 2 本の射は一致する。 -/
theorem hom_ext (h : IsCore X) {Y : 𝒞} (f g : Y ⟶ X) : f = g :=
  h.isTerminal.hom_ext f g

/-- コアへの hom 集合は subsingleton。 -/
theorem subsingleton_hom (h : IsCore X) (Y : 𝒞) : Subsingleton (Y ⟶ X) :=
  ⟨fun f g => h.hom_ext f g⟩

/-- **`k`-core の自己準同型は恒等のみ**(Hoshi §17: `Aut_K(C_K) = {id}`)。 -/
theorem subsingleton_end (h : IsCore X) : Subsingleton (X ⟶ X) :=
  h.subsingleton_hom X

/-- **`k`-core の自己同型群は自明**。Phase 1 の `Aut_K(X_K) ≅ F_l ⋊ {±1}` の計算は、
`C_K` がこの意味でコアであること(自己同型が恒等のみ)に依拠している。 -/
theorem subsingleton_aut (h : IsCore X) : Subsingleton (Aut X) :=
  ⟨fun a b => Iso.ext (h.hom_ext a.hom b.hom)⟩

/-- **コアは(一意的な)同型を除いて一意**。2 つの `k`-core の間には標準的同型が存在する。 -/
noncomputable def uniqueIso (h : IsCore X) (h' : IsCore X') : X ≅ X' where
  hom := h'.isTerminal.from X
  inv := h.isTerminal.from X'
  hom_inv_id := h.hom_ext _ _
  inv_hom_id := h'.hom_ext _ _

end IsCore

end IUT.Anabelian
