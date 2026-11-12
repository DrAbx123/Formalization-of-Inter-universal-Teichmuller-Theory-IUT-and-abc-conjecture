# TATE-IN-FAMILY — 显式 I_n 族的 M(n) 与大 n 失效

日期：2026-11-12；qpilot（A1025）。**Sage（构造/局部验证）+ Python（公式）**；**MODEL，不是 Lean**。

## 1. 显式 Tate 族

取 p=7, ℓ=5（p≠ℓ），n=1..50：
```
E_n := EllipticCurve_from_j(-1/7^n).minimal_model()
```
等价 Weierstrass 形式为 `y² + xy = x³ + a4(n) x + a6(n)`（由 Sage 的 j-构造给出；如 n=1: `a4=-252, a6=169351`）。

Sage 局部验证（每个 n）：
- 在 p=7 的 reduction type = **bad split multiplicative**；
- Kodaira symbol = **I_n**；
- `v_7(Δ_min)=n`；`v_7(conductor)=1`；
- 因此局部 Tate 参数阶为 n。

**限制**：这些全局曲线在其它素数上可能有额外坏约化（`E_n.is_semistable()` 为 False），所以本测试是对**局部位 p=7** 的 c1 MODEL-PAPER 项，不声称全局半稳定曲线族；c1 的 M 只需局部位。

## 2. c1 MODEL-PAPER 公式（单坏位 p=7, ℓ=5, nC=2, sF=2.5, e=2ℓ=10）

```
H_tame = nC·(1−1/e)·log p = 2·0.9·log7 = 3.502638
Ind2(n) = Σ_{j=1}^{nC} frac(j²·n/(2ℓ))·log p = Σ_{j=1}^2 frac(j² n/10)·log7
T(n) = (sF−1)·n·logp/(2ℓ) = 1.5·n·log7/10 = 0.2918865·n
arch = arch_for_nC(2) = (arch_defect(2)+arch_defect(3))/2 = 0.28527176
M(n) = arch + H_tame + Ind2(n) − T(n)
```
（T 按题目给 `(sF−1)v/(2ℓ)`，**不除 nC**；e=2ℓ 的 H 是常数，不随 n 变；Ind2 周期有界。）

## 3. M(n) 与 n*

| n | I_n | H_tame | Ind2(n) | T(n) | M(n) | admissible |
|---|---:|---:|---:|---:|---:|---|
| 1 | I1 | 3.502638 | 0.972955 | 0.291887 | **4.713729** | yes |
| 2 | I2 | 3.502638 | 1.945910 | 0.583773 | 5.394798 | yes |
| 5 | I5 | 3.502638 | 0.972955 | 1.459433 | 3.546183 | no |
| 10 | I10 | 3.502638 | 0.000000 | 2.918865 | 1.113795 | no |
| 15 | I15 | 3.502638 | 0.972955 | 4.378298 | 0.627318 | no |
| 18 | I18 | 3.502638 | 1.945910 | 5.253957 | 0.479863 | yes |
| 19 | I19 | 3.502638 | 2.918865 | 5.545844 | 1.160931 | yes |
| **20** | I20 | 3.502638 | 0.000000 | 5.837730 | **−2.049820** | no（5\\|20） |
| **21** | I21 | 3.502638 | 0.972955 | 6.129617 | **−1.368752** | **yes**（first admissible negative） |
| 24 | I24 | 3.502638 | 1.945910 | 7.005277 | −1.271456 | yes |
| 30 | I30 | 3.502638 | 0.000000 | 8.756596 | −4.968686 | no |
| 50 | I50 | 3.502638 | 0.000000 | 14.594326 | −10.806416 | no |

**结果**：
- **n* = 20**（第一个 M<0 的 n；但 5|20，不满足 ℓ∤n 的 admissible 条件）；
- **第一个 admissible 负值 n*_adm = 21**；
- n≥20 后 M(n) 随 n 线性下降，n=50 已到 −10.81；31/50 个 n 为负。

## 4. 结论

1. 显式局部 Tate 族 I_n（n=1..50）下，c1 MODEL-PAPER 的 `M(n)` 在 **n=20** 翻负，第一个 admissible 负值为 **n=21**；
2. 这与 A1018 的合成外推一致：`H_tame+Ind2+arch` 有界，而 `T(n)` 线性增长，导致大 n 必负；
3. **模型内 variant 大 n 失效**；若 qOrder 无界且 (UB) 不提供小界，需要补随 n 线性增长的正项（如 LGP/theta hull 的 q^{j²} 正缩放或 exact orderVol/different），否则 M≥0 不成立；
4. 本测试是局部 MODEL，不声称全局半稳定族；全局曲线 `E_n` 的其它坏位未计入。

## 文件
- `coord/tate_in_family.csv`（n=1..50: n,Kodaira,vp,H,Ind,T,arch,M,admissible,neg）
- `tmp/tate_family_7_local.json`（Sage 局部验证原始数据）
- 本文件 `coord/TATE-IN-FAMILY.md`