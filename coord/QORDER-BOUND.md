# QORDER-BOUND — qOrder 能否有界/恒 1？(A1023)

| field | value |
|---|---|
| Status | **DECISION: qOrder = n（I_n 的 n），整数、无界；恒 1 与界均不成立** |
| 源 | `Iut/Cor312/ThetaData/Basic.lean:171-194`：`qOrder := qOrderAt`，`qOrder_eq_orderNat`（tateParam.toOrdered.orderNat），`qOrder_pos`，`coprime_qOrder`；`AdmissiblePrime:52-55`；`Multiradial/ThetaData.lean:152` (`¬ l ∣ qOrder`)；`Concrete/ThetaLocalConstruct/Data.lean:327-330` `ordp_qrootOf` |

## 1. qOrder 的精确定义（lana 源）

`Iut/Cor312/ThetaData/Basic.lean:171-177`：
```
noncomputable def qOrder (w) (hw) : Nat := qOrderAt D.E (D.mult_of_mem_bad hw)
lemma qOrder_eq_orderNat : D.qOrder w hw = ((D.tateParam w hw).toOrdered (isUniformizer_unifAt w)).orderNat
```
即 qOrder = Tate 参数 `q_w` 相对 **uniformizer** 的**归一化整数阶**（`orderNat`）；
`:184-189 orderNat_eq_qOrder`：与 uniformizer 选择无关（一致化子不变性）；
`AdmissiblePrime:51-53`："its normalized integer order is `Iut.qOrderAt` (`Iut.InitialThetaData.qOrder`),
independent of the uniformizer"。

关键：**qOrder 是整数**（Nat），不是 `n/(2l)`、不是 `n·2l`；对半稳定 `I_n` 曲线，
`v_w(q_w) = n` ⇒ **qOrder = n**。`qroot` 的阶是 `n/(2l·ramIdx F w)`（Data.lean:330），
即 qOrder 除以 2l 和 e_w 才是 qroot 的 ordp；两者不能混淆。

## 2. Definition 3.1 的约束（全部，无界）

源级约束只有：
1. `qOrder_pos`（Basic:180-182）：`0 < qOrder`（正）；
2. `coprime_qOrder`（Basic:191-194）：`Nat.Coprime l (qOrder w hw)`（l 与 n 互素）；
3. `q_order_coprime`（AdmissiblePrime:152 字段）：对**每个** uniformizer/ Tate 参数形式成立（为了无选择）；
4. `Multiradial/ThetaData.lean:152`: `(hP2 : forall w, ¬ l ∣ qOrder w hw)`（同上，互素表述）。

**没有**任何上界、没有 `qOrder = 1`、没有只允许有限多个 n 的条件。
半稳定 `I_n` 的 n 可任意大；对每个 n 都存在 admissible l（取 l>n 的素数即可，
因要求仅 `l ∤ n`），故 **qOrder 无界 ⇒ 大 m 问题不能靠有界 qOrder 消失**。

## 3. 具体曲线数值

| curve | 退化类型 | p | qOrder = v_p(q_Tate) | 说明 |
|---|---|---|---|---|
| 11a1 | I5 | 11 | **5** | qOrder=5（整数）；l 需 ∤5，取 l=7,11,13... |
| 858k2 | I21 | 13 | **21** | qOrder=21；l∤21，取 l=5,11,13（l=7 不可） |
| 9546f3 | I72 | — | **72** | qOrder=72 |
（表达式：`qOrder w hw = (tateParam w hw).toOrdered.orderNat`；对 F=Q 且标准 uniformizer 即 n）

## 4. 结论与影响

1. **qOrder = n，恒 1 不成立、无上界**；Def 3.1 只给正性与 l 互素；
2. A1018 的 `M 随 m 线性下降` 问题**仍存在**；ind2 为 frac/有界（A1022），不能抵消；
3. 因此若 paper variant 对任意 admissible 成立，必须有**其他正线性项**，或在 M 展开中
   我们漏了某个与 m 同阶的项。候选（按优先级）：
   - `logShellRadius(scaled)`：`componentVol_leastHull_tensorLogShell_eq = Σ logShellRadius·logp`（VcI:603）；
     对 scaled shell 的半径是否含 `+ord(a)` 需读 `leastHull_tensorLogShell_eq`/`componentVol_prod_incl_smul_integral`；
   - `orderVol`/`shellExcess`：VcI:102/313-319（`orderVol <= 0`、`|shellDefect+orderVol| <= Σ(3+log e)`，有界）；
   - `logVol_lgp_integral = −sF·A`（IdentifiedCopies:444）已计入（负线性）；
   - `PacketIndexForm`（VcI:634-640）：`mu(R_I) = −½(d_I − d_T)logp`，`d` 可能与 n 无界相关；
   - 或实现级：`rhs` 的 variant 形式（ivLabels）与 paper 的 literal 读法差异。
4. 若无此正线性项：**必须承认需要 (UB) 或 admissible 额外界**；否则大 n 下 variant 与
   `M>=0` 在本文形式化中不成立（与 paper 矛盾），应作为形式化缺口上报。

## 5. 下一步

1. 精确算 `componentVol_prod_incl_smul_integral`（ScaleVolume:46/118）与
   `leastHull_tensorLogShell_eq`，确认 scaled radius 是否有 `+ordp(a)` 正项；
2. 若有 ⇒ 它可与 qScale 负项抵消（A1020 的直觉对、A1022 的 frac 结论是另一条 rounding 修正），
   写精确的 `ind2 = linear + frac` 分解；
3. 若没有 ⇒ 写 `! M>=0` 的大 n 反例框架与 (UB) 条件引理，上报 lead。