# SYMBOLIC-CANCELLATION — 巨大初等项展开 + 相消 + 残余符号

日期：2026-11-13；qpilot（A1081）。**SymPy/Python**；脚本 `tools/symbolic_cancel.py`；无 Lean/Sage。

## 1. 符号模型（索引 i,v,c,j）

索引：`i` capsule, `v` place, `c` label/tuple, `j` label-pow。

```
sF = (nC+1)(2nC+1)/6
packetWeight: Σ_c w_c = 1（单 label 时 w=1）
hullPacket(i,v) = Σ_c w_c Σ_j (1−1/e_{cj}) logp = nC(1−1/e)logp
V = (1/nC)Σ_i hullPacket = nC(1−1/e)logp
ind2(i,v) = Σ_c w_c Σ_j frac(j²m/(2ℓ)) logp = F logp, 0≤F≤nC
gap = (1/nC)Σ_i ind2 = F logp
qScale_j = −j² m logp/(2ℓ);  ind2Leading_j = +j² m logp/(2ℓ)
A = m logp/(2ℓ)
```

## 2. 符号相消

Σ_{j=1..nC} j² = nC·sF（sF=(nC+1)(2nC+1)/6）。

```
qScale_sum + ind2Leading_sum
  = −(Σ_j j²)m logp/(2ℓ) + (Σ_j j²)m logp/(2ℓ)
  = −nC sF m logp/(2ℓ) + nC sF m logp/(2ℓ) = 0
```
SymPy 输出：`qscale+ind2lead = 0`。

## 3. 残余表达式

```
R = V + gap − (sF−1)A + arch + shell
  = nC(1−1/e)logp + F logp − (sF−1)m logp/(2ℓ) + arch + shell
  = logp·[ F + nC(1−1/e) − (sF−1)m/(2ℓ) ] + arch + shell
```
（SymPy 未化简形式：`(e*l*(F*logp+arch+shell) - e*logp*m*((nC+1)(2nC+1)-6)/12 + l*logp*nC*(e-1))/(e*l)`。）

**残余只剩少数项**：`∝logp` 的 `F` 与 `nC(1−1/e)`、`∝m logp` 的负项、常数 `arch+shell`；没有新的正 q-linear 项。

## 4. 正性条件

```
R ≥ 0  ⇔  F + nC(1−1/e) + (arch+shell)/logp ≥ (sF−1)m/(2ℓ)
因 0 ≤ F ≤ nC，充分条件：
m ≤ mcrit := 2ℓ/(sF−1) · [ nC(2−1/e) + (arch+shell)/logp ]
```
对 l=5, nC=2, e=2ℓ=10, logp=log7, arch=0.28527, shell=0：**mcrit = 26.31**。

## 5. 参数测试（m 到 10^6）

网格：m ∈ {1,5,10,20,24,25,26,30,50,100,1000,10^4,10^5,10^6}，F∈{0,1,2}：共42点；**29 个 R<0，13 个 R>0**。

- m≤25 的点基本全正（R 随 F 增大）；
- m=26 附近按 mcrit=26.31 临界；
- m≥100 后全部负；m=10^4 时 R≈−2915（F=0）；m=10^6 更负。

**符号判定：R 对 m 线性下降；m 超过 mcrit≈26.3（l=5）后必负。** 大 m 无正线性项抵消。

## 6. 结论

1. 逐 j 的 qScale 与 ind2 leading **精确相消**（SymPy 0），用 `Σj²=nC sF`；
2. 残余 = `logp(F+nC(1−1/e)) − (sF−1)m logp/(2ℓ) + arch + shell`，只有少数项；
3. 残余对 m 的斜率 `−(sF−1)logp/(2ℓ)<0`（sF>1）；大 m 必负，临界 mcrit≈26.3（l=5）；
4. 若要 m→∞ 仍正，必须补**随 m 线性增长的正项**（LGP/theta hull 正 q^{j²} 缩放、exact orderVol/different 等）；当前符号模型没有。

## 文件
- `tools/symbolic_cancel.py`（可复跑）
- `coord/symbolic_cancellation_results.json`（R、qscale+ind2lead、mcrit、42点测试）
- 本文件 `coord/SYMBOLIC-CANCELLATION.md`