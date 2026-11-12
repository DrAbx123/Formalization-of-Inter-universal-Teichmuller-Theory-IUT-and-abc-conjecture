# T4-BRIDGE — theta-hull volume 与 Faltings height/omega 度量的比较 (A1105)

| field | value |
|---|---|
| Status | ANALYSIS + GAP RECORD (no Lean; no compile) |
| 判定 | **C**：T4 桥（`R` 与 `h_F` 的**方向性比较**）在现有经典结果中**没有已证方向**；已知结果只是 `h_F` 与 conductor/discriminant 的界，或 theta/Faltings 度量的**归一化等式**（等价，不是不等式） |
| 关联 | NERON-TATE-FEASIBLE.md §2、NERON-TATE-ROUTE.md (T4) |

## 1. T4 桥的精确陈述（几种候选形式）

记
```
R   := |log Θ| = -S2717ThetaHullLogVolume = -log( Haar(θ-hull region) )   （A1104 §1.2）
h_F := Faltings height of E/K（相对对偶层 ω = det Hodge 的 Faltings 度量）
c   := 常数（可依赖 K、ℓ、局部数据）
```
候选形式：
```
(T4-geq)  R ≥ h_F + c            （theta-hull 下界 Faltings height）
(T4-leq)  R ≤ h_F + c            （上界）
(T4-prod) R ≥ c1 * h_F + c2      （线性比较）
(T4-eq)   R = h_F + c            （精确归一化等式）
```
目标 `−A ≤ −R`（A=|log q|）在 (T4-eq) 下变成 `A ≥ h_F + c`，仍需 `A` 与 `h_F` 的显式比较（A1104 §2）。

## 2. 已知经典结果（可提供的方向）

### 2.1 Faltings height 的显式公式（等式，A）
```
h_F(E) = (1/[K:Q]) Σ_σ log( (1/2) ∫_{E_σ(C)} |ω|² )      （定义/经典）
log|q| = 12 ( h_F + (1/[K:Q])Σ_σ log η_σ + 常数 )           （Tate/Kronecker，LITERATURE）
```
⇒ 提供 `log|q|` 与 `h_F` 的**等式**（A）；但不涉及 `R`。

### 2.2 Noether 公式 / 判别式关系（等式/不等式）
```
Noether 型：12 h_F 与 log|Δ|、conductor、arch 修正的关系（经典；精确形式依赖归一化）
已知高度界（文献）：h_F(E) ≥ -c1 log N_E - c2（下界，c1>0）；h_F(E) ≥ -c3（绝对下界）
Szpiro 型：h_F 的上界 ⇔ Szpiro/ABC 型不等式（非定理）
```
⇒ 只给 `h_F` 与 **conductor/discriminant** 的界，**没有** `h_F` 与 `R`（theta-hull）的比较。

### 2.3 theta/Faltings 度量的归一化（等式，A 条件）
```
theta 度量与 Faltings 度量在归一化下可能满足  -log||θ||_F = h_F + 常数   （归一化事实）
但这是**等式的选择/定义**（metric normalization），不是方向性不等式；
且我们的 R 是 Haar 体积（负 log），不是直接的 Faltings 度量。
```
⇒ 等价关系（若成立）**不蕴含** T4 的方向性不等号；相反，它把比较变成同一对象的两种写法。

## 3. 判定：是否存在已证方向？

| 候选 | 类型 | 理由 |
|---|---|---|
| (T4-geq) `R ≥ h_F + c` | **无已证方向（C）** | 经典界只涉及 `h_F` vs conductor/Δ；无 `h_F` vs θ-hull volume |
| (T4-leq) `R ≤ h_F + c` | **无已证方向（C）** | 同上；方向上界也缺 |
| (T4-prod) 线性比较 | **C** | 同上 |
| (T4-eq) 归一化等式 | **A 条件（若度量识别完成）** | 是归一化事实，不是不等式；且需 q-pilot/θ 度量识别 |
| 用 Noether/Faltings 高度界推出一侧 | **C** | 界的形式不同（conductor 而非 θ-hull） |

**结论：T4 桥只有“等价/归一化”候选，没有已证的任一方向 ⇒ 判 C，并记录为 GAP-T4。**

## 4. 若要走通需要什么

```
(1) 度量识别：q-pilot/θ-hull 的 Haar log-volume 与 Faltings/theta 度量（ω）的显式关系；
(2) 局部 arch 展开：η/θ 值与 Faltings height 的逐 embedding 展开；
(3) 解析不等式：R 与 h_F 的方向性比较（或 R 与 log|q| 的直接比较）；
(4) 一般 K 的归一化（1/[K:Q]、ω 选取）。
```
当前仓库：`qOrder`/`ordp_qrootOf`/Faltings 标量部分可用；Tate/Néron 模型、theta 度量、
θ-hull 与 Faltings 的联系均缺（GAP-TATE-BUNDLE/GAP-METRIC）。

## 5. Lean 签名草案（条件形式，标注 UNPROVED）

```lean
/-- T4 bridge candidates: directional comparison between R and h_F. -/
def T4Geq (R hF c : Real) : Prop := hF + c ≤ R
def T4Leq (R hF c : Real) : Prop := R ≤ hF + c
def T4Eq  (R hF c : Real) : Prop := R = hF + c

/-- Conditional use: T4-geq + explicit A >= hF + c gives the target. -/
theorem target_of_T4Geq {A R hF c : Real} (hT4 : T4Geq R hF c) (hA : hF + c ≤ A) :
    -A ≤ -R := by
  unfold T4Geq at hT4
  linarith

/-- Record: no proved direction is available in the current repo/classical inputs. -/
def GAP_T4 : Prop := T4Geq 0 0 0 ∨ T4Leq 0 0 0   -- placeholder marker (UNPROVED)
```

## 6. 结论

1. T4 桥的精确形式：`R ≥ h_F + c`、`R ≤ h_F + c`、线性比较、归一化等式；
2. 经典 Faltings/Noether 结果只给 `h_F` 与 conductor/Δ 的关系（且多为等式/下界），
   **没有** `h_F` 与 θ-hull volume 的方向性比较；
3. theta/Faltings 度量归一化只给等式（A 条件），不是不等式；
4. 因此 T4 桥**无已证方向** ⇒ 判定 **C**，记录 GAP-T4；
5. 若走 NERON-TATE 路线，必须新增 (1)-(4)；在此之前 T4 不能作为证明链的一环。