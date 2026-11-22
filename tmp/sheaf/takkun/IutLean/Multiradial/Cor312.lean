import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.MainTheorem

/-!
# [IUT-III] Corollary 3.12 — 主不等式の形式的導出

底本: [IUT-III] Thm 3.11, Cor 3.12 / 星裕一郎入門 §12。

**Corollary 3.12**(IUT の中心不等式): `−|log(Θ)| ∈ ℝ` かつ
  `−|log(Θ)| ≥ −|log(q)|`
―― ここで `−|log(Θ)|` は「(Ind1),(Ind2),(Ind3) の不定性のもとでの Θ標対象の**可能な像すべて**の
和集合の**正則包** (holomorphic hull) の(プロセッション正規化された単解的)対数体積」、
`−|log(q)|` は「q標対象の像の対数体積」(不定性なし)。

**証明の構造**([IUT-III] の「1 ページの導出」): Theorem 3.11 の多輻的アルゴリズムを認めれば、
1. Θ×μ_LGP-link は Θ標対象を q標対象に貼り合わせ、Thm 3.11 (iii) の両立性により
   **q標対象は Θ標対象の可能な像のひとつ**に含まれる(`containment`);
2. 正則包は可能な像すべてを含む(`hull_spec`);
3. 対数体積の**単調性**(`vol_mono`)により `vol(q標) ≤ vol(正則包)`、すなわち
   `−|log(q)| ≤ −|log(Θ)|`。∎

本モジュールはこの導出を **`sorry` 無しで完全に形式化**する(`cor312`)。

**honest 注記(本プロジェクトで最も重要な注記)**: この形式化により、Cor 3.12 の成立は
`PilotVolumeData` の**インスタンス供給** ―― とりわけ `containment` フィールド
(= Thm 3.11 (iii) の Θ×μ_LGP-link 両立性を、プロセッション正規化された体積の意味で成立させる
こと)―― に**精密に還元**される。数学界の係争(Scholze–Stix 2018 vs Mochizuki)は、まさに
「実際の Hodge 劇場データからこの `containment` が(主張された正規化の独立性のもとで)構成
できるか」を巡るものである。本形式化は係争を解決しないが、**係争点を単一の構造体フィールド
として厳密に特定**する ―― 将来の形式検証が到達すべき正確な標的。
-/

namespace IUT.Multiradial

universe u v

/-- **Cor 3.12 の設定データ**: 対数殻の領域(包含順序付き)・不定性群 `Γ = (Ind1)×(Ind2)` の
作用・(プロセッション正規化された)対数体積・Θ標対象・q標対象・正則包・そして
**多輻的両立性 `containment`**(Thm 3.11 (iii)、唯一の深い入力 = 係争点)。 -/
structure PilotVolumeData where
  /-- 対数殻の領域の型(包含順序付き)。 -/
  Ω : Type u
  [ord : Preorder Ω]
  /-- 不定性群 `Γ = (Ind1) × (Ind2)`。 -/
  Γ : Type v
  [group : Group Γ]
  [action : MulAction Γ Ω]
  /-- **対数体積**(プロセッション正規化された単解的 log-volume)。値が `ℝ`(有限)である
  ことは対数殻のコンパクト性の反映(Cor 3.12 の「`−|log(Θ)| ∈ ℝ`」部分)。 -/
  vol : Ω → ℝ
  /-- 体積の**単調性**: 大きい領域は大きい体積([IUT-III] Prop 3.9 の体積両立性の核)。 -/
  vol_mono : Monotone vol
  /-- Θ標対象(の多輻的表示における像)。 -/
  thetaPilot : Ω
  /-- q標対象の像(不定性を施さない)。 -/
  qPilot : Ω
  /-- **正則包** (holomorphic hull): Θ標対象の可能な像すべての和集合を含む領域。 -/
  hull : Ω
  /-- 正則包は不定性軌道(可能な像すべて)を含む((Ind3) 上半両立性ゆえ包を取る必要がある)。 -/
  hull_spec : ∀ g : Γ, g • thetaPilot ≤ hull
  /-- ★ **多輻的両立性**(**注意: このフィールドは「q標と Θ標が同一の体積空間 `Ω` 内で
  比較可能である」ことを前提しており、それ自体が [IUT-III] Thm 3.11 から Cor 3.12 への
  架橋段階 ―― 送信側 `ℝ` と受信側 `ℝ` の同一視 ―― を含む**。Thm 3.11 自体の主張ではない)。
  係争(Scholze–Stix)はまさにこの単一空間比較の正当性にある。2 つの `ℝ` を分離した
  honest な定式化と空虚性定理は `Multiradial/TwoSidedLink.lean` を参照。 -/
  containment : ∃ g : Γ, qPilot ≤ g • thetaPilot

attribute [instance] PilotVolumeData.ord PilotVolumeData.group PilotVolumeData.action

namespace PilotVolumeData

variable (P : PilotVolumeData.{u, v})

/-- `−|log(Θ)|` := 正則包の対数体積。 -/
def negLogTheta : ℝ := P.vol P.hull

/-- `−|log(q)|` := q標対象の像の対数体積。 -/
def negLogQ : ℝ := P.vol P.qPilot

/-- **[IUT-III] Corollary 3.12(形式的導出)**: `−|log(Θ)| ≥ −|log(q)|`。

証明([IUT-III] の「1 ページの導出」の忠実な形式化): `containment` により q標対象は
可能な像 `g • Θ標` に支配され、`hull_spec` により可能な像は正則包に含まれ、
`vol_mono` により体積が比較される。∎

(`−|log(Θ)| ∈ ℝ` の有限性主張は `vol : Ω → ℝ` に内蔵。)deep な部分はすべて
`PilotVolumeData` のインスタンス供給(とりわけ `containment` = Thm 3.11)に単離されている。 -/
theorem cor312 : P.negLogQ ≤ P.negLogTheta := by
  obtain ⟨g, hg⟩ := P.containment
  exact (P.vol_mono hg).trans (P.vol_mono (P.hull_spec g))

/-- Cor 3.12 設定の不定性データは、既存の (Ind1),(Ind2),(Ind3) 形式
(`LogShellIndeterminacy`、多輻的 well-definedness 証明済み)と両立する。 -/
def toIndeterminacy : LogTheta.LogShellIndeterminacy where
  Γ := P.Γ
  I := P.Ω
  ind3 := LogTheta.upperSemiCompatibility P.Γ P.Ω

/-- Cor 3.12 設定における多輻的表示は well-defined(不定性のもとで不変)。 -/
theorem multiradial_wellDefined :
    MultiradialWellDefined P.toIndeterminacy :=
  multiradialWellDefined P.toIndeterminacy

end PilotVolumeData

/-- **witness**(枠組みの非空性): 自明な Cor 3.12 設定。`Ω = ℝ`(領域の大きさ)、
自明な不定性、`vol = id`、`q標 = 0 ≤ Θ標 = 正則包 = 1`。 -/
def trivialPilotVolumeData : PilotVolumeData where
  Ω := ℝ
  Γ := PUnit
  action := { smul := fun _ x => x, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }
  vol := id
  vol_mono := monotone_id
  thetaPilot := 1
  qPilot := 0
  hull := 1
  hull_spec := fun _ => le_refl 1
  containment := ⟨PUnit.unit, zero_le_one⟩

/-! ## IUT-IV への数値的架橋 ― プロセッション正規化定数 `l(l+1)/12` -/

/-- **プロセッション正規化された Θ標次数の閉形式**: 奇数 `l` に対し
`12 · θ = l⋆ · l · (l+1)`、すなわち正規化次数 `θ/l⋆ = l(l+1)/12`。
これは [IUT-IV] Thm 1.10 の高さ評価に現れる**正確な定数**(`−|log(Θ)|` の展開で
Gauss 分布 `q^{j²}` の `j = 1,…,l⋆` にわたる平均から生じる)。 -/
theorem twelve_mul_thetaPilotDegree (l : ℕ) (hodd : Odd l) :
    12 * thetaPilotDegree l = lStar l * (l * (l + 1)) := by
  have h6 := six_mul_thetaPilotDegree l
  have hl : 2 * lStar l + 1 = l := IUT.two_mul_lStar_add_one l hodd
  calc 12 * thetaPilotDegree l
      = 2 * (6 * thetaPilotDegree l) := by ring
    _ = 2 * (lStar l * (lStar l + 1) * (2 * lStar l + 1)) := by rw [h6]
    _ = lStar l * ((2 * lStar l + 1) * (2 * lStar l + 1 + 1)) := by ring
    _ = lStar l * (l * (l + 1)) := by rw [hl]

end IUT.Multiradial
