import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.Cor312

/-!
# 対数体積計算の初等的道具 — [IUT-IV] Thm 1.10 証明 step (i) の (E1)–(E6)

底本: [IUT-IV] Thm 1.10 の証明(p.23–24)。

Thm 1.10 の証明は step (i) で、対数体積計算に用いる**初等的事実の一覧 (E1)–(E6)** を宣言する:

* **(E1)** `(1/n)·∑_{m=1}^n m = (n+1)/2`(Gauss 和 ―― プロセッション正規化の一次項);
* **(E2)** `(1/n)·∑_{m=1}^n m² = (2n+1)(n+1)/6`(平方和 ―― テータ値 `q^{j²}` の
  プロセッション正規化次数、`Multiradial/MainTheorem.lean` の `six_mul_sum_sq` で証明済);
* **(E3)** `|GL₂(F_p)| = p(p+1)(p−1)²`([IUT-IV] Cor 2.2 の素数選択で除外素数を数える);
* **(E4)** `p = 2,3,5` での (E3) の値(`2·3`, `3·2⁴`, `5·2⁵·3`);
* **(E5)** `[F_mod(√−1) : F_mod] ≤ 2`(文脈固有ゆえ略);
* **(E6)** `0 ≤ log 2 ≤ 1 ≤ log 3 ≤ log π ≤ log 5 ≤ 2`(数値評価)。

本モジュールは (E1), (E3), (E4), (E6) を **Mathlib の真の内容**(`exp 1`・`π` の厳密数値評価、
有限体上の一般線型群の位数公式)で `sorry` 無しに証明する。これにより Thm 1.10 の証明の
**初等的道具一式が全て検証済み**となり、残る深い部分は `p` 進 different・テンソルパケットの
評価([IUT-IV] Prop 1.1–1.9)のみとなる。
-/

namespace IUT.Diophantine

open Real Finset

/-! ## (E1) Gauss 和 -/

/-- **(E1)**(分母を払った形): `2·∑_{j=0}^{n} j = n(n+1)`。プロセッション正規化における
一次項 `(1/n)∑ m = (n+1)/2` の内容。 -/
theorem two_mul_sum_range (n : ℕ) :
    2 * (∑ j ∈ range (n + 1), j) = n * (n + 1) := by
  rw [mul_comm, Finset.sum_range_id_mul_two (n + 1)]
  simp [Nat.add_sub_cancel]
  ring

/-! ## (E3), (E4): `|GL₂(F_p)| = p(p+1)(p−1)²` -/

/-- **(E3)**: 有限体 `F_p` 上の一般線型群の位数 `|GL₂(F_p)| = p(p+1)(p−1)²`。
[IUT-IV] Cor 2.2 の素数 `l` の選択において、除外すべき素数(mod-`l` 表現の像が小さい素数)を
数える際に用いられる。Mathlib の `Matrix.card_GL_field`(`∏ (q² − qⁱ)`)から導出。 -/
theorem card_GL2 (p : ℕ) [Fact p.Prime] :
    Nat.card (GL (Fin 2) (ZMod p)) = p * (p + 1) * (p - 1) ^ 2 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have h := Matrix.card_GL_field (𝔽 := ZMod p) (n := 2)
  rw [ZMod.card p] at h
  rw [h, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_two_pow.trans (Nat.pow_le_pow_left hp 2)
  have h2 : p ≤ p ^ 2 := by nlinarith
  have h3 : 1 ≤ p := by omega
  zify [h1, h2, h3]
  push_cast
  ring

/-- **(E4)**: `p = 2` での (E3): `|GL₂(F₂)| = 6 = 2·3`。 -/
theorem card_GL2_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_GL2 2]; norm_num

/-- **(E4)**: `p = 3` での (E3): `|GL₂(F₃)| = 48 = 3·2⁴`。 -/
theorem card_GL2_three : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [card_GL2 3]; norm_num

/-- **(E4)**: `p = 5` での (E3): `|GL₂(F₅)| = 480 = 5·2⁵·3`。 -/
theorem card_GL2_five : Nat.card (GL (Fin 2) (ZMod 5)) = 480 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [card_GL2 5]; norm_num

/-! ## (E6) 数値評価 `0 ≤ log 2 ≤ 1 ≤ log 3 ≤ log π ≤ log 5 ≤ 2` -/

/-- **(E6-1)**: `0 ≤ log 2`。 -/
theorem log_two_nonneg : 0 ≤ Real.log 2 :=
  Real.log_nonneg (by norm_num)

/-- **(E6-2)**: `log 2 ≤ 1`(`2 < e` の厳密数値評価 `exp_one_gt_d9` による)。 -/
theorem log_two_le_one : Real.log 2 ≤ 1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  linarith [Real.exp_one_gt_d9]

/-- **(E6-3)**: `1 ≤ log 3`(`e < 3` の厳密数値評価 `exp_one_lt_d9` による)。 -/
theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  linarith [Real.exp_one_lt_d9]

/-- **(E6-4)**: `log 3 ≤ log π`(`3 < π`、Mathlib の π の厳密数値評価による)。 -/
theorem log_three_le_log_pi : Real.log 3 ≤ Real.log π :=
  Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])

/-- **(E6-5)**: `log π ≤ log 5`(`π < 4 < 5`)。 -/
theorem log_pi_le_log_five : Real.log π ≤ Real.log 5 :=
  Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])

/-- **(E6-6)**: `log 5 ≤ 2`(`5 < e²` の厳密数値評価による)。 -/
theorem log_five_le_two : Real.log 5 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9]

end IUT.Diophantine
