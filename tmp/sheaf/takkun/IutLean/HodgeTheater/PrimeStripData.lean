import Mathlib
import tmp.sheaf.takkun.IutLean.Combinatorics.Fl
import tmp.sheaf.takkun.IutLean.Frobenioid.PrimeStripSystem

/-!
# Hodge 劇場の素点縞系データ — `HasPrimeStripSystem` の脱ブラックボックス化

底本: [IUT-I] §4–§6 (Def 5.2, Cor 6.10), [IUT-II] §4 (Cor 4.6 symmetrizing isomorphisms),
星裕一郎入門 §17, §20, §25 / Phase D プライム縞インフラ(`Frobenioid/PrimeStripSystem.lean`)。

旧 `opaque HasPrimeStripSystem (l : ℕ) : Prop` は「素点縞の系が `F_l⋊±`/`F_l⋆` 対称性・
テータ値・Kummer 理論と両立する」という、当時は**表現手段が無かった**条件の黒箱だった。
Phase D で構築した 12 層のプライム縞インフラ(4 種プライム縞・対称化同型付きラベル付き系・
Gaussian テータ値・Kummer 円分指標)により、この条件は**具体的なデータ構造**として表現可能に
なった。本モジュールで:

* **`GeoSym l = F_l⋊±` の `LabCusp± = F_l` へのアフィン作用**(Hoshi §17 の幾何学的対称性、
  `r i • x = x - i`(並進)、`sr i • x = i - x`(反転))を `MulAction` として構成・証明;
* **`PrimeStripSystem l`** ―― Hodge 劇場の素点縞系の具体的データ構造:
  - `addSystem`: `F_l⋊±` 対称化同型付きの加法的ラベル付きプライム縞系([IUT-II] Cor 4.6);
  - `mulSystem`: `F_l⋆` 対称化同型付きの乗法的ラベル付きプライム縞系;
  - `gaussian`: Gaussian プライム縞(テータ値 `q_v^{j²}` の入れ物);
  - `glue`: 加法的縞のモノ解析的核が Gaussian 縞の核と貼り合う(定数プライム縞
    `F⊩_△` の同一視、[IUT-II] Thm A (i));
  - `nondegenerate`: テータ値の**非退化性**(`V^bad ≠ ∅` / q-parameter 非単数の反映、
    自明な witness を排除する本質的条件);
* テータ値の `±1` 対称性(`theta_symmetric`)と Kummer 円分指標(`kummer`)が**すべての**
  素点縞系で自動的に成立・付随することを証明。

**honest 注記**: 幾何学的実現(楕円曲線 `E` のエタールテータ関数・緩基本群から実際にこの
データを構成すること)は Mathlib 未整備の曲線幾何を要し、本構造の**インスタンス供給**として
将来の課題に残る。しかし条件そのものはもはや黒箱ではなく、全て具体的に表現されている。
-/

namespace IUT.HodgeTheater

open IUT.Frobenioid

/-! ## 幾何学的対称性 `F_l⋊±` のアフィン作用(Hoshi §17) -/

/-- **幾何学的対称性のアフィン作用**: `F_l⋊± = DihedralGroup l` が加法的カスプラベル
`LabCusp± = F_l` にアフィン変換で作用する ―― 回転 `r i` は並進 `x ↦ x - i`、鏡映 `sr i` は
反転付き並進 `x ↦ i - x`。`Aut_K(X_K) ≅ F_l⋊±` のカスプへの作用(Hoshi §17)。 -/
instance instMulActionGeoSymLabCuspPM (l : ℕ) : MulAction (GeoSym l) (LabCuspPM l) where
  smul g x := match g with
    | .r i => x - i
    | .sr i => i - x
  one_smul x := by
    show x - 0 = x
    exact sub_zero x
  mul_smul a b x := by
    rcases a with i | i <;> rcases b with j | j
    · show x - (i + j) = x - j - i
      ring
    · show (j - i) - x = (j - x) - i
      ring
    · show (i + j) - x = i - (x - j)
      ring
    · show x - (j - i) = i - (j - x)
      ring

@[simp] theorem geoSym_r_smul (l : ℕ) (i x : Fl l) :
    (DihedralGroup.r i : GeoSym l) • (x : LabCuspPM l) = x - i := rfl

@[simp] theorem geoSym_sr_smul (l : ℕ) (i x : Fl l) :
    (DihedralGroup.sr i : GeoSym l) • (x : LabCuspPM l) = i - x := rfl

/-- 鏡映 `sr 0` はラベルの負化 `x ↦ -x`(`±1` 対称性、零カスプ `0` を固定 ―― `Fl.lean` の
`neg_eq_self_iff` 零カスプ一意性と接続)。 -/
theorem geoSym_sr_zero_smul (l : ℕ) (x : LabCuspPM l) :
    (DihedralGroup.sr 0 : GeoSym l) • x = -x := by
  rw [geoSym_sr_smul, zero_sub]

/-! ## Hodge 劇場の素点縞系(具体的データ構造) -/

/-- **Hodge 劇場の素点縞系** ([IUT-I] §4–§6, [IUT-II] Cor 4.6): 旧 `opaque HasPrimeStripSystem`
の脱ブラックボックス化。素点集合 `V` 上の:
* 加法的ラベル `LabCusp± = F_l` 付きプライム縞系と `F_l⋊±` **対称化同型**(`addSystem`);
* 乗法的ラベル `LabCusp = F_l⋆` 付きプライム縞系と `F_l⋆` **対称化同型**(`mulSystem`);
* テータ値 `q_v^{j²}` を担う **Gaussian プライム縞**(`gaussian`);
* 加法的縞と Gaussian 縞の**モノ解析的核の貼り合わせ**(`glue`、定数プライム縞 `F⊩_△` の同一視);
* テータ値の**非退化性**(`nondegenerate`、`V^bad ≠ ∅` の反映 ―― 自明な系を排除する)。

テータ値の `±1` 対称性(`theta_symmetric`)と Kummer 円分指標(`kummer`)は自動的に付随する。 -/
structure PrimeStripSystem (l : ℕ) [Fact l.Prime] where
  /-- 素点の集合 `V`。 -/
  V : Type
  /-- 加法的(`F_l⋊±` 対称性)ラベル付きプライム縞系([IUT-II] Cor 4.6 (iii))。 -/
  addSystem : LabeledPrimeStripSystem.{0} V (LabCuspPM l) (GeoSym l)
  /-- 乗法的(`F_l⋆` 対称性)ラベル付きプライム縞系([IUT-I] Cor 6.10)。 -/
  mulSystem : LabeledPrimeStripSystem.{0} V (LabCusp l) (LabCusp l)
  /-- Gaussian プライム縞(テータ値 `q_v^{j²}` の入れ物、[IUT-II] Cor 4.6 (v))。 -/
  gaussian : GaussianPrimeStrip.{0, 0, 0} V
  /-- **貼り合わせ**: 各ラベルの加法的縞のモノ解析的核は Gaussian 縞の核と同型
  (定数プライム縞 `F⊩_△` の同一視、[IUT-II] Thm A (i))。 -/
  glue : ∀ t : LabCuspPM l,
    DhPrimeStripEquiv ((addSystem.strip t).toDh) gaussian.toFhPrimeStrip.toDhPrimeStrip
  /-- **非退化性**: ある素点でテータ値 `q_v^{j²}` が全ての `j ≠ 0` に対し非自明
  (`V^bad ≠ ∅`、q-parameter が非単数=無限位数であることの反映)。 -/
  nondegenerate : ∃ v : V, ∀ j : ℤ, j ≠ 0 → gaussian.thetaValueAt v j ≠ 1

namespace PrimeStripSystem

variable {l : ℕ} [Fact l.Prime] (S : PrimeStripSystem l)

/-- **テータ値の `±1` 対称性は全ての素点縞系で自動的に成立**(Gauss 分布 `(-j)² = j²`、
Hoshi §18 のラベル理論との両立)。データに要求せず**証明される**。 -/
theorem theta_symmetric (v : S.V) (j : ℤ) :
    S.gaussian.thetaValueAt v (-j) = S.gaussian.thetaValueAt v j :=
  GaussianPrimeStrip.thetaValueAt_neg _ _ _

/-- **Kummer 円分指標は全ての素点縞系に自動的に付随**: Gaussian 縞の Galois 作用が
Frobenius 的円分物 `Λ(Mon_v)` への円分指標を誘導(Kummer 理論との両立、Phase D 第五層)。 -/
noncomputable def kummer (v : S.V) :
    S.gaussian.G v →* MulAut (IUT.Cyclotome.FrobeniusCyclotome (S.gaussian.Mon v)) :=
  S.gaussian.toFhPrimeStrip.cyclotomicCharacter v

end PrimeStripSystem

/-- **素点縞系の存在**(旧 `opaque HasPrimeStripSystem` の後継): 具体的データ構造
`PrimeStripSystem l` が存在すること。もはや黒箱ではない具体的命題。 -/
def HasPrimeStripSystem (l : ℕ) [Fact l.Prime] : Prop :=
  Nonempty (PrimeStripSystem l)

end IUT.HodgeTheater
