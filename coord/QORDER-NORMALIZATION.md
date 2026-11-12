# QORDER-NORMALIZATION — qOrder 是否模 2ℓ/约化代表元？(A1026)

| field | value |
|---|---|
| Status | **DECISION: qOrder 是原始整数阶 `v_π(q)`（I_n → n），无模/约化；Def 3.1 只要求正性 + 与 ℓ 互素；I_n 大 n 警报成立** |
| 源 | `Iut/Cor312/ThetaData/TateParameterAt.lean:108-124` (`qOrderAt := toOrdered unifAt .orderNat`, `qOrderAt_pos`, `orderNat_eq_qOrderAt`), `Iut/Cor312/ThetaData/Basic.lean:171-194` (`qOrder := qOrderAt`, `qOrder_eq_orderNat`, `qOrder_pos`, `coprime_qOrder`), `AdmissiblePrime.lean:152-156` (`q_order_coprime` on `toOrdered`), `Iut/Concrete/ThetaLocalConstruct/Data.lean:327-330` (`ordp_qrootOf` 用原始 qOrder) |

## 1. qOrder 的精确定义（无模运算）

`TateParameterAt.lean:108-114`：
```
noncomputable def qOrderAt ... : Nat :=
  ((tateParameterAt E hw).toOrdered (isUniformizer_unifAt w)).orderNat
theorem qOrderAt_pos : 0 < qOrderAt E hw   -- 正性，Nat
```
`Basic.lean:171-194`：
```
noncomputable def qOrder w hw : Nat := qOrderAt D.E (D.mult_of_mem_bad hw)
lemma qOrder_eq_orderNat : D.qOrder w hw = ((D.tateParam w hw).toOrdered (isUniformizer_unifAt w)).orderNat := rfl
theorem orderNat_eq_qOrder : (t.toOrdered hπ).orderNat = D.qOrder w hw   -- uniformizer 无关
theorem qOrder_pos : 0 < D.qOrder w hw
theorem coprime_qOrder : Nat.Coprime D.l (D.qOrder w hw)
```
即 qOrder = `orderNat` = **相对 uniformizer 的整数阶 v_π(q)**；
- 无 `ZMod`、无 `Int.emod`、无 mod 2ℓ/ℓ；
- 无固定区间/代表元选择；
- `q_order_coprime`（AdmissiblePrime:152-156）是对 `(t.toOrdered hπ).PrimeToOrder l` —— 
  即对**原始整数阶** `orderNat` 的互素条件（对所有 uniformizer 一致），
  不是模值；
- `ordp_qrootOf`（Data:327-330）明确用 `qOrder/(2ℓ·ramIdx)`，即 qroot 的 ordp 是原始 qOrder 除以 2ℓ·e；
  所以 qOrder 本身是**未除 2ℓ** 的原始整数。

## 2. 对 I_n 的数值

半稳定 `I_n`：Tate 参数 `q` 的 `v_π(q) = n` ⇒ **qOrder = n**（原始整数）。

| curve | I_n | p | qOrder（原始，lana 定义） | 假设「mod 2ℓ」读法（**无源支持**） |
|---|---|---|---|---|
| 11a1 | I5 | 11 | **5** | l=5: 5 mod 10 = 5；l=7: 5 mod 14 = 5；l=11: 5 mod 22 = 5 |
| 858k2 | I21 | 13 | **21** | l=5: 21 mod 10 = **1**；l=7: 21 mod 14 = 7；l=11: 21 mod 22 = 21 |
| 9546f3 | I72 | ? | **72** | l=5: 72 mod 10 = **2**；l=7: 72 mod 14 = 2；l=13: 72 mod 26 = 20 |

注意：右边「mod 2ℓ」列仅为回答 lead 的假设而列，**lana 源无任何 mod/约化**；
`orderNat` 是 Nat 正数，`coprime_qOrder` 对原始 n 要求 `gcd(ℓ,n)=1`（不是 gcd(ℓ, n mod 2ℓ)）。
若 21 被读成 `21 mod 10 = 1`，则 Def 3.1(c) 的互素条件会对 n=21 与 ℓ=5 自动成立，
但这与 `coprime_qOrder` 的字面（`Nat.Coprime ℓ (qOrder)`）不符：ℓ=5, n=21 时 gcd(5,21)=1 ✓ 本就成立；
ℓ=7 时 gcd(7,21)=7 ⇒ 排除（与原始读法一致，与 mod 读法无关）。

## 3. 结论

1. **qOrder = 原始整数阶 v_π(q)**（I_n ⇒ n），非模 2ℓ/ℓ、非约化代表元；
2. Def 3.1 的约束只有：`qOrder > 0` 与 `Nat.Coprime ℓ qOrder`（原始阶）；无固定区间；
3. 因此 **I_n 大 n 警报成立**：qOrder 无界 ⇒ A = qOrder·logp/(2ℓ) 线性无界；
4. 不能靠「qOrder 取模」消除大 n 问题；仍需 (a) GAP-GAP-MLINEAR（gap 的正 m-项）或
   (b) 显式 q 有界/高度界假设（`VariantBoundedQ B`）；
5. 若 paper 的 variant 实际隐含高度界或 q 的界，应在形式化陈述中显式写出（否则与 paper 偏差）。

## 4. Lean 陈述（源端口/草案）

```lean
/-- qOrder is the raw integer order (lana `qOrder_eq_orderNat`, Basic:176-177). -/
theorem qOrder_raw (D : InitialThetaData) (w : FinitePlace D.F)
    (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    D.qOrder w hw = ((D.tateParam w hw).toOrdered (isUniformizer_unifAt w)).orderNat := rfl

/-- Positivity (lana `qOrder_pos`). -/
theorem qOrder_pos' (D) (w) (hw) : 0 < D.qOrder w hw := D.qOrder_pos w hw

/-- Coprimality with the raw order (lana `coprime_qOrder`). -/
theorem qOrder_coprime' (D) (w) (hw) : Nat.Coprime D.l (D.qOrder w hw) :=
  D.coprime_qOrder w hw
```
（无 mod/emod 版本；如后续需要 `qOrder mod 2ℓ` 的界，应作为**额外**假设登记，不是 lana 定义。）

## 5. 待办

- 把本结论同步到 `coord/VARIANT-QSTABILITY.md` 的「环节 3」：排除「qOrder 取模」这一救活可能；
- 聚焦 GAP-GAP-MLINEAR（gap 的 m-展开）或 `VariantBoundedQ` 显式假设。