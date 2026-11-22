import Mathlib
import tmp.sheaf.takkun.IutLean.LogTheta.LogShell

/-!
# log-Kummer 対応 (log-Kummer correspondence)

底本: [IUT-III] Prop 3.5, Thm 3.11 (ii), Thm A (ii) / 星裕一郎入門 §9–§10。

**log-Kummer 対応**は、log-theta-lattice の垂直列(対数リンクで結ばれた Hodge 劇場の列)に
おいて、各レベル `m` の **Frobenius 的データ**(モノイド・対数殻)を、全レベル共通の
**垂直核**(エタール的データ、vertical coricity)へ **Kummer 同型**で関係付ける機構である。
その決定的性質が:

* **(Ind3) 上半両立性** (upper semi-compatibility): レベル `m` の Kummer 像とレベル `m+1` の
  (対数リンクで転送した)Kummer 像は**等しくなく**、包含 `⊆` のみが成り立つ
  ([IUT-III] Thm A (ii): 非アルキメデス素点で自然な包含、アルキメデスで自然な全射)。
  このため全レベルの比較は**像の合併(とその正則包)**を強制する ―― Cor 3.12 の
  `−|log(Θ)|` に正則包が現れる形式的根拠。
* **「1 の巾根 ↦ 0 = 不定性なし」**([IUT-III] Thm A (ii) 原文: "multiplication by roots of
  unity corresponds, via the log-link, to an addition by zero indeterminacy, i.e., to
  **no indeterminacy**!"): テータ値・`F_mod` の Kummer 理論の 1 の巾根不定性は、対数写像で
  零へ潰れる ―― 分裂単項式・`F_mod` の写しが(Ind3 に**さらされない**)厳密な両立性を持つ理由。

本モジュールは両者を `sorry` 無しで形式化する:
`kummer_le_transport`(Kummer 像の増大鎖 = 合併の強制)と
`logMap_rootOfUnity`(1 の巾根の消滅 = 不定性なし)。
-/

namespace IUT.LogTheta

universe u v

/-- **log-Kummer 対応**: 垂直核 `D`(エタール的、全レベル共通)、各レベル `m ∈ ℕ` の
Frobenius 的データ `F m`、対数リンク `log : F m → F (m+1)`、Kummer(像)写像
`kummer : F m → D`、そして **(Ind3) 上半両立性**(Kummer 像はリンクに沿って増大)。 -/
structure LogKummerCorrespondence where
  /-- 垂直核(エタール的データの領域、vertical coricity により全レベル共通)。 -/
  D : Type u
  [ordD : Preorder D]
  /-- 各レベル `m` の Frobenius 的データの領域。 -/
  F : ℕ → Type v
  [ordF : ∀ m, Preorder (F m)]
  /-- 対数リンク(レベル `m` から `m+1` へ)。 -/
  log : ∀ m, F m → F (m + 1)
  /-- Kummer 写像: 各レベルの Frobenius 的データを垂直核の言葉へ。 -/
  kummer : ∀ m, F m → D
  /-- ★ **(Ind3) 上半両立性**([IUT-III] Thm A (ii)): レベル `m` の Kummer 像は、
  対数リンクで転送した次レベルの Kummer 像に**含まれる**(等号ではない!)。 -/
  upperSemi : ∀ (m : ℕ) (x : F m), kummer m x ≤ kummer (m + 1) (log m x)

attribute [instance] LogKummerCorrespondence.ordD LogKummerCorrespondence.ordF

namespace LogKummerCorrespondence

variable (K : LogKummerCorrespondence.{u, v})

/-- レベル `m` から `n` 段の対数リンク反復による転送 `F m → F (m + n)`。 -/
def transport (m : ℕ) : (n : ℕ) → K.F m → K.F (m + n)
  | 0 => id
  | n + 1 => fun x => K.log (m + n) (transport m n x)

@[simp] theorem transport_zero (m : ℕ) (x : K.F m) : K.transport m 0 x = x := rfl

/-- **Kummer 像の増大鎖**(log-Kummer 対応の核心): 上半両立性の反復により、レベル `m` の
Kummer 像は任意段数 `n` の転送像の Kummer 像に含まれる ―― 各レベルの像は垂直核の中で
**増大列**をなす。ゆえに全レベルにわたる比較は像の**合併(とその正則包)**を取ることを
強制する([IUT-III] Cor 3.12 の「possible images の union の hull」の形式的根拠)。 -/
theorem kummer_le_transport (m : ℕ) (x : K.F m) :
    ∀ n : ℕ, K.kummer m x ≤ K.kummer (m + n) (K.transport m n x)
  | 0 => le_refl _
  | n + 1 =>
      (kummer_le_transport m x n).trans (K.upperSemi (m + n) (K.transport m n x))

/-- **包の支配条件**: 垂直核の領域 `hull` が、レベル `0` の対象 `x0` の全レベル転送像の
Kummer 像をすべて支配する(Cor 3.12 の正則包が満たすべき条件の log-Kummer 版)。 -/
def HullDominates (x0 : K.F 0) (hull : K.D) : Prop :=
  ∀ n : ℕ, K.kummer (0 + n) (K.transport 0 n x0) ≤ hull

/-- 包が全レベルを支配すれば、特に基底レベルの Kummer 像を支配する。 -/
theorem base_le_hull {x0 : K.F 0} {hull : K.D} (h : K.HullDominates x0 hull) :
    K.kummer 0 x0 ≤ hull :=
  h 0

/-- **増大性による還元**: どこか 1 つのレベル `n` の転送像を支配すれば、増大鎖により
基底レベルの像は自動的に支配される(鎖の単調性 ―― 包条件の本質は「上方」にある)。 -/
theorem base_le_of_level (x0 : K.F 0) (hull : K.D) (n : ℕ)
    (h : K.kummer (0 + n) (K.transport 0 n x0) ≤ hull) :
    K.kummer 0 x0 ≤ hull :=
  (K.kummer_le_transport 0 x0 n).trans h

end LogKummerCorrespondence

/-- **自明な log-Kummer 対応**(witness): 全レベル `ℝ`、リンク・Kummer とも恒等。
上半両立性は等号(包含の特別な場合)で成立。枠組みの非空性。 -/
def trivialLogKummer : LogKummerCorrespondence.{0, 0} where
  D := ℝ
  F _ := ℝ
  log _ := id
  kummer _ := id
  upperSemi _ x := le_refl x

/-! ## 「1 の巾根 ↦ 0 = 不定性なし」([IUT-III] Thm A (ii)) -/

/-- **1 の巾根の消滅**([IUT-III] Thm A (ii) の正確な内容): 対数リンクの定義域の
**1 の巾根**(テータ値・`F_mod` の Kummer 理論に現れる唯一の不定性)は、対数写像により
`0`(「零の加算」)へ移る ―― すなわち**不定性なし**。対数殻がねじれなし(`ℝ` ベクトル空間型、
`NoZeroSMulDivisors ℕ`)であることによる。分裂単項式(テータ値)と `F_mod` の写しが
log-Kummer 対応において (Ind3) にさらされず**厳密に**両立する理由。 -/
theorem logMap_rootOfUnity {U : Type u} [CommGroup U] {S : LogShell.{v}}
    (L : LogLink U S) [NoZeroSMulDivisors ℕ S.carrier]
    (u : U) (n : ℕ) (hn : n ≠ 0) (hu : u ^ n = 1) :
    L.logMap (Additive.ofMul u) = 0 := by
  have h : n • L.logMap (Additive.ofMul u) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, hu, ofMul_one, map_zero]
  rcases smul_eq_zero.mp h with h0 | h0
  · exact absurd h0 hn
  · exact h0

end IUT.LogTheta
