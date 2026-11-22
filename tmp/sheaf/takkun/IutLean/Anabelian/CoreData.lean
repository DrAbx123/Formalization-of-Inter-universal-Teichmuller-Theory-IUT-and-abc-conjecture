import Mathlib
import tmp.sheaf.takkun.IutLean.Anabelian.Core
import tmp.sheaf.takkun.IutLean.Combinatorics.Fl

/-!
# K-core データ ([IUT-I] Def 3.1(d) の脱ブラックボックス化)

底本: [IUT-I] Def 3.1(d), §1 / [CanLift] Remark 2.1.1 / [EtTh] §2 冒頭 / Hoshi §17。

「`C_K` が `K`-core である」とは、**`C_K` を有限エタール射で関連付ける双曲的軌道曲線の圏
`Loc_K(C_K)` において `C_K` が終対象**であること([CanLift] Rem 2.1.1)。終対象性そのもの
(`IsCore`)は `Anabelian/Core.lean` で完全形式化済み。旧 `opaque IsKCore` に残っていたのは
「圏 `Loc_K(C_K)` と、その中の `C_K`・`X_K` という**実際の幾何学的対象**」の欠如だった。

本モジュールはこれを **`KCoreData`(具体的データ構造)** で表す ―― 圏 `Loc`・対象 `C_K`/`X_K`・
被覆 `X_K → C_K`・**忠実な `F_l⋊±` デッキ作用**(`Gal(X_K/C_K) ≅ F_l⋊±`、[IUT-I] §1 の
型 `(1, l-tors)±` 構造)・そして **`IsCore C_K`(終対象性 = K-core 性、Def 3.1(d) の条件
そのもの)**。帰結として:

* `Aut_K(C_K)` の自明性(Hoshi §17 の `Aut_K(C_K) = {1}`)―― `IsCore.subsingleton_aut` から
  **証明される**;
* デッキ変換群の位数 `2l`(`|F_l⋊±| = 2l`)―― 忠実性から**証明される**。

**honest 注記**: 幾何学的実現(楕円曲線 `E` から実際の軌道曲線 `C_K = C_F ×_F K` とその
被覆圏を構成し、この `KCoreData` のインスタンスを供給すること)は、スキーム/スタックの
エタール被覆理論(`CurvePi1.lean` の Galois 圏基盤がその受け皿)を要する将来の課題として
残る。しかし条件 (d) そのものはもはや黒箱ではなく、終対象性・対称性・被覆構造として
すべて具体的に表現されている。`MonoThetaEnvironment.thetaGroup`・`PrimeStripSystem` と
同じ honest データパターン。
-/

namespace IUT.Anabelian

open CategoryTheory

/-- **K-core データ** ([IUT-I] Def 3.1(d)): 圏 `Loc`(= `Loc_K(C_K)`、`C_K` にエタール射で
関連付く軌道曲線の圏)の中の対象 `C_K`・`X_K`、被覆 `X_K → C_K`、忠実な `F_l⋊±` デッキ作用
(`Gal(X_K/C_K) ≅ F_l⋊±`)、および **`C_K` の終対象性 = K-core 性**(Def 3.1(d) の条件)。 -/
structure KCoreData (l : ℕ) where
  /-- 圏 `Loc_K(C_K)`(`C_K` と有限エタール射で関連付く双曲的軌道曲線の圏)。 -/
  Loc : Type
  [cat : Category.{0} Loc]
  /-- 軌道曲線 `C_K = C_F ×_F K`。 -/
  CK : Loc
  /-- 曲線 `X_K`(型 `(1, l-tors)` の被覆)。 -/
  XK : Loc
  /-- 被覆射 `X_K → C_K`(次数 `2l` の有限エタール被覆)。 -/
  cover : XK ⟶ CK
  /-- **デッキ変換**: `Gal(X_K/C_K) ≅ F_l⋊±` の実現([IUT-I] §1、Hoshi §17 の
  `Aut_K(X_K) ⊇ F_l⋊±`)。 -/
  deck : GeoSym l →* Aut XK
  /-- デッキ作用は忠実(`F_l⋊±` が被覆の対称性として真に実現される)。 -/
  deck_injective : Function.Injective deck
  /-- デッキ変換は被覆射と両立(被覆 `X_K → C_K` のファイバーを保つ)。 -/
  cover_equivariant : ∀ g : GeoSym l, (deck g).hom ≫ cover = cover
  /-- **K-core 性**([IUT-I] Def 3.1(d) の条件そのもの): `C_K` は `Loc` の終対象。 -/
  core : IsCore CK

attribute [instance] KCoreData.cat

namespace KCoreData

variable {l : ℕ} (D : KCoreData l)

/-- **`Aut_K(C_K)` は自明**(Hoshi §17 の `Aut_K(C_K) = {1}`)。K-core 性(終対象性)から
**証明される帰結**(`IsCore.subsingleton_aut`)。 -/
theorem aut_CK_subsingleton : Subsingleton (Aut D.CK) :=
  D.core.subsingleton_aut

/-- 任意の対象から `C_K` への射は一意(K-core への射の一意性)。 -/
theorem hom_to_CK_unique {Y : D.Loc} (f g : Y ⟶ D.CK) : f = g :=
  D.core.hom_ext f g

/-- **デッキ変換群は位数 `2l`**: 忠実な `F_l⋊±` 作用の像の位数は `|F_l⋊±| = 2l`
(Hoshi §17、被覆 `X_K → C_K` の次数)。 -/
theorem card_deck_range [Fact l.Prime] : Nat.card (Set.range D.deck) = 2 * l := by
  rw [Nat.card_range_of_injective D.deck_injective, Nat.card_eq_fintype_card]
  exact card_GeoSym l

end KCoreData

/-! ## witness: 2 対象の Loc 圏モデル(枠組みの非空性) -/

/-- witness 用の 2 対象圏の対象: `X_K` と `C_K`。 -/
inductive LocModel (l : ℕ) : Type
  | XK : LocModel l
  | CK : LocModel l

namespace LocModel

variable {l : ℕ}

/-- Hom 集合: `Hom(X_K, X_K) = F_l⋊±`(デッキ変換群)、`Hom(−, C_K) = PUnit`(`C_K` 終対象)、
`Hom(C_K, X_K) = ∅`(コアへは行けるが戻れない)。 -/
@[reducible] def Hom : LocModel l → LocModel l → Type
  | .XK, .XK => GeoSym l
  | .XK, .CK => PUnit
  | .CK, .XK => PEmpty
  | .CK, .CK => PUnit

instance : Category.{0} (LocModel l) where
  Hom := Hom
  id X := match X with
    | .XK => (1 : GeoSym l)
    | .CK => PUnit.unit
  comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | .XK, .XK, .XK, f, g => g * f
    | .XK, .XK, .CK, _, _ => PUnit.unit
    | .XK, .CK, .CK, _, _ => PUnit.unit
    | .CK, .CK, .CK, _, _ => PUnit.unit
    | .XK, .CK, .XK, _, g => g.elim
    | .CK, .XK, _, f, _ => f.elim
    | .CK, .CK, .XK, _, g => g.elim
  id_comp {X Y} f := by
    cases X <;> cases Y
    · exact mul_one f
    · rfl
    · exact f.elim
    · rfl
  comp_id {X Y} f := by
    cases X <;> cases Y
    · exact one_mul f
    · rfl
    · exact f.elim
    · rfl
  assoc {W X Y Z} f g h := by
    cases W <;> cases X <;> cases Y <;> cases Z <;>
      first
        | rfl
        | exact f.elim
        | exact g.elim
        | exact h.elim
        | exact (mul_assoc h g f).symm

/-- `C_K` は終対象(すべての対象から `C_K` への射が一意に存在)。 -/
def isTerminalCK : Limits.IsTerminal (CK : LocModel l) :=
  Limits.IsTerminal.ofUniqueHom
    (fun X => match X with
      | .XK => PUnit.unit
      | .CK => PUnit.unit)
    (fun X m => by cases X <;> rfl)

/-- デッキ変換 `g : F_l⋊±` の与える `X_K` の自己同型。 -/
def deckIso (g : GeoSym l) : (XK : LocModel l) ≅ XK where
  hom := g
  inv := (g⁻¹ : GeoSym l)
  hom_inv_id := inv_mul_cancel g
  inv_hom_id := mul_inv_cancel g

/-- デッキ変換群準同型 `F_l⋊± →* Aut(X_K)`。 -/
def deckHom : GeoSym l →* Aut (XK : LocModel l) where
  toFun := deckIso
  map_one' := Iso.ext rfl
  map_mul' _ _ := Iso.ext rfl

theorem deckHom_injective : Function.Injective (deckHom (l := l)) :=
  fun _ _ h => congrArg Iso.hom h

end LocModel

/-- **`KCoreData` の witness**(枠組みの非空性): 2 対象 Loc 圏モデル。`C_K` の終対象性・
忠実な `F_l⋊±` デッキ作用・被覆両立性がすべて `sorry` 無しで成立する具体例。 -/
def trivialKCoreData (l : ℕ) : KCoreData l where
  Loc := LocModel l
  CK := .CK
  XK := .XK
  cover := PUnit.unit
  deck := LocModel.deckHom
  deck_injective := LocModel.deckHom_injective
  cover_equivariant := fun _ => rfl
  core := ⟨LocModel.isTerminalCK⟩

end IUT.Anabelian
