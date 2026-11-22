import Mathlib
import tmp.sheaf.takkun.IutLean.Combinatorics.Fl
import tmp.sheaf.takkun.IutLean.Theta.ThetaValues
import tmp.sheaf.takkun.IutLean.LogTheta.Indeterminacy

/-!
# 主定理: 多輻的表示と Θ-pilot / q-pilot

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§12 / [IUT-III] Def 3.8, Thm 3.11, Cor 3.12。

* **q 標対象** (q-pilot object): q パラメータ `q_E` が定める数論的直線束。
* **Θ 標対象** (Θ-pilot object): テータ値 `(q_E^{j²/2l})_{j=1,…,l⋆}` が定める数論的直線束。

主定理(多輻的表示, [IUT-III] Cor 3.12)は、Θ リンクと多輻的アルゴリズムを併せることで
  `|deg(q 標対象)| ≥ -vol((Ind1),(Ind2),(Ind3) による Θ 標対象の軌道の和集合の正則包)`
を導く。これが `|deg L|` の上からの評価、ひいては Diophantus 的不等式 (Phase 9) を与える。

本ファイルでは、Θ 標対象の次数を支配する **Gauss 和 `∑_{j=1}^{l⋆} j²`** を完全証明し、それが
`l³` のオーダー(正確には `24·θ + l = l³`)であることを示す ―― これが高さ評価の `l³` 増大の源。
主不等式そのものは IUT 全体の帰結ゆえ `MultiradialRepresentation` として保留する。
-/

namespace IUT.Multiradial

open IUT IUT.Theta Finset

/-- **Gauss 和**(平方和の公式): `6·∑_{j<n+1} j² = n(n+1)(2n+1)`。 -/
theorem six_mul_sum_sq (n : ℕ) :
    6 * ∑ j ∈ range (n + 1), j ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

/-- **Θ 標対象の(組合せ的)次数**: ラベル `j = 1,…,l⋆` 上の Gauss 指数 `j² = gaussExp j` の和
`∑_{j=1}^{l⋆} j²`。Θ 標対象はテータ値 `(q^{j²/2l})_{j=1,…,l⋆}` が定める直線束 ([IUT-III] Def 3.8)。 -/
def thetaPilotDegree (l : ℕ) : ℕ := ∑ j ∈ range (lStar l + 1), j ^ 2

/-- Θ 標対象次数の Gauss 和による閉形式。 -/
theorem six_mul_thetaPilotDegree (l : ℕ) :
    6 * thetaPilotDegree l = lStar l * (lStar l + 1) * (2 * lStar l + 1) :=
  six_mul_sum_sq (lStar l)

/-- **Θ 標対象次数の `l³` 閉形式**: `l` が奇数(IUT では `l ≥ 5` の素数)のとき
`24 · θ + l = l³`、すなわち `θ = (l³ − l)/24`。Θ 標対象の次数が `l³` のオーダーで増大すること
―― これが高さ(q 標対象の次数)の評価における `l³` 増大の源である。 -/
theorem twentyFour_mul_thetaPilotDegree_add (l : ℕ) (hodd : Odd l) :
    24 * thetaPilotDegree l + l = l ^ 3 := by
  have h6 := six_mul_thetaPilotDegree l
  have hl : 2 * lStar l + 1 = l := IUT.two_mul_lStar_add_one l hodd
  have e1 : 24 * thetaPilotDegree l
      = 4 * (lStar l * (lStar l + 1) * (2 * lStar l + 1)) := by
    have h2 : 24 * thetaPilotDegree l = 4 * (6 * thetaPilotDegree l) := by ring
    rw [h2, h6]
  have arith : ∀ s : ℕ, 4 * (s * (s + 1) * (2 * s + 1)) + (2 * s + 1) = (2 * s + 1) ^ 3 := by
    intro s; ring
  calc 24 * thetaPilotDegree l + l
      = 4 * (lStar l * (lStar l + 1) * (2 * lStar l + 1)) + l := by rw [e1]
    _ = 4 * (lStar l * (lStar l + 1) * (2 * lStar l + 1)) + (2 * lStar l + 1) := by rw [hl]
    _ = (2 * lStar l + 1) ^ 3 := arith (lStar l)
    _ = l ^ 3 := by rw [hl]

/-- 上式より `24 · θ = l³ − l`。 -/
theorem twentyFour_mul_thetaPilotDegree (l : ℕ) (hodd : Odd l) :
    24 * thetaPilotDegree l = l ^ 3 - l := by
  have := twentyFour_mul_thetaPilotDegree_add l hodd
  omega

/-- **多輻的表示の well-definedness**: object (a) の多輻的出力(= 不定性群 Γ の作用の軌道)が、
不定性 (Ind1),(Ind2) を施しても不変であること。 -/
def MultiradialWellDefined (D : LogTheta.LogShellIndeterminacy) : Prop :=
  ∀ (x : D.I) (g : D.Γ), D.multiradialOutput (g • x) = D.multiradialOutput x

/-- **多輻的表示の well-definedness は証明できる**(`output_eq_of_indeterminate` より)。

旧 `opaque MultiradialRepresentation` のうち *証明可能な核* ―― 多輻的出力が不定性のもとで
well-defined であること ―― を実際に証明したもの。これにより主定理の「object (a) が
(Ind1),(Ind2) という不定性のもと多輻的に表示される」という部分が `sorry` 無しで確立される。

残る真に深い部分 ―― `‡q 標対象 が ‡Θ 標対象 の不定性軌道の正則包に体積的に含まれる`
という**不等式** ([IUT-III] Cor 3.12, `|deg(q標)| ≥ -vol(Θ標軌道)`)―― は、対数体積と
Θ リンクの両立性を要し、`Diophantine.DiophantineMainTheorem` の主張へ繋がる。 -/
theorem multiradialWellDefined (D : LogTheta.LogShellIndeterminacy) :
    MultiradialWellDefined D :=
  fun x g => D.output_eq_of_indeterminate x g

end IUT.Multiradial
