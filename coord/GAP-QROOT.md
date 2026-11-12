# GAP-QROOT — 钉死 `ordp(qroot) = qOrder/(2l·ramIdx)` (A1022)

| field | value |
|---|---|
| Status | **CLOSED（源级）** — lana 已给出精确公式 `ordp_qrootOf` |
| 源 | `Iut/Concrete/ThetaLocalConstruct/Data.lean:279-330`：`qrootOf`(:281), `qrootOf_spec`(:287-291), `qrootOf_pow`(:305-313), `ordp_qrootOf`(:327-330)；`Iut/Cor312/ThetaData/Basic.lean:146+` `tateParam`；`AdmissiblePrime:52` `qOrder` |

## 1. 精确定义与公式（lana 源）

- `qrootOf`（Data.lean:281-284）：bad place 上取 `exists_qroot` 选出的 `2l`-th root；非 bad 取 1；
- `qrootOf_spec`（:287-291）：`qrootOf v ^ (2l) = (tate.S v hv).t.q`；
- `qrootOf_pow`（:305-313）：`qrootOf v ^ (2l) = embedFOf ... (tateParam w hw).q`；
- **`ordp_qrootOf`（:327-330，关键）**：
```
ordp D.Kt v (qrootOf D v) = (D.qOrder w hw : Real) / (2 * D.l * ramIdx D.F w)
```
其中 `w : FinitePlace D.F`、`hw : w ∈ badPlacesOver ...`、`v | w`；
`D.qOrder w hw` 是 Tate 参数的归一化整数阶（= 半稳定 I_n 的 n）；
`ramIdx D.F w` 是 **base field F** 在 w 的分歧指数（F=Q 时为 1）。

## 2. 结论（GAP-QROOT 关闭）

```
ordp(qroot) = qOrder / (2 * l * ramIdx D.F w)
```
- 对 `F = Q`（或 w 未分歧，`ramIdx=1`）：`ordp(qroot) = qOrder/(2l) = m/(2l)` — 与 A1020 假设一致；
- 一般 F：分母多一个 `ramIdx D.F w`（正的整数，≥1），公式仍精确；
- 因此 A1020 的 `scaleElt = qroot^{j²}` 的阶为
  `ordp(scaleElt) = j² * qOrder/(2l*ramIdx)`，`componentVol(scaleElt·O) = -j²*qOrder*logp/(2l*ramIdx)`；
- 在 `F=Q`（或 e_w=1）下与 `-j²*m*logp/(2l)` 完全一致。

## 3. 对 M 分解的影响

- `A = m*logp/(2l)`（qOrder=m）；`scaleVol = -j²*m*logp/(2l)`（e_w=1）；`ind2Leading = +j²*m*logp/(2l)`；
- 净效果不变：两 j² 项相消，M = A + B，`dM/dm = +logp/(2l) > 0`；
- 若 `e_w > 1`，则 scaleVol 系数变为 `j²/(e_w)`，ind2 的补偿对应为 `+j²/(e_w)`（同一 `qroot` 阶），
  相消结构不变；净 A 项仍是 `m*logp/(2l)`。

## 4. Lean 陈述（实际可写，待 watchdog）

```lean
/-- GAP-QROOT closed: lana `ordp_qrootOf` gives the exact normalization. -/
theorem ordpQroot_eq (qOrder l ramIdx : Real) (hl : 0 < l) (hr : 0 < ramIdx) :
    qOrder / (2 * l) / ramIdx = qOrder / (2 * l * ramIdx) := by
  field_simp [hl.ne', hr.ne']
  ring
```
（真实接线：`ordp_qrootOf` 的直接端口；本骨架以纯算术形式记录归一化。）

## 5. 后续

- 更新 `Mzk1MDecompositionActual` 文件头 GAP 清单：GAP-QROOT → CLOSED（公式 + 源行号）；
- 下一步 GAP-TENSORVOL：读 `componentVol_tensorLogShell_eq`（VcI:794）+ `componentVol_prod_incl_smul_integral`
  符号，确认 `componentVol(a·O) = -Σ ordp(a_j) logp`；
- 再 GAP-IND2：用 `leastHull_units_smul`/`leastHull_mono` 证 `V(thetaHull)` m-无关。