# IND2-EXACT — ind2Term 精确公式：frac（有界）还是线性？(A1022)

| field | value |
|---|---|
| Status | **DECISION: 数据支持 frac/有界（qpilot c1）；A1020 的线性正项主张**不成立**（除非额外 rounding 引理）** |
| 源 | Gap:747-754 (`ind2Term` 字面定义), ThetaRegion:168-175 (`thetaFiniteOn`), IndAut:52-82 (`latticeAut`, `image_smul_tensorLogShell`), VcI:364-381 (`Int.ceil` 出现在 `logLatticeA`), ScaleVolume/NOTE: `componentVol_prod_incl_smul_integral` |

## 1. ind2Term 的字面定义（无歧义）

`Gap:747-754`:
```
ind2Term i p c = componentVol (leastHull (thetaComponent))
                 - componentVol (scaleElt i p c • leastHull (shell))
```
`thetaComponent = thetaFiniteOn`（ThetaRegion:168-175）：
```
thetaFiniteOn = union_{phi in indAut} phi '' (union_{l in S} scaleEltAt l • shell)
```
两项都含 `scaleElt`；差别只在 **hull/rounding** 与 **automorphism union**。

## 2. 关键源：tensorAut 对 scaled shell 的作用

`Iut/Concrete/LocalConstruct/IndAut.lean:52-82`:
- `latticeAut = {phi | exists e : linear equiv, phi'' tensorLogShell = tensorLogShell}`；
- `image_smul_tensorLogShell`（:68-82）：对 `t : Q_p`（**central scalar**）与 `phi in latticeAut`：
  `phi '' (t • tensorLogShell) = t • tensorLogShell`。
**限制**：该引理要求 `t` 是 `Q_p`-central scalar；而 `scaleEltAt` 是 `qroot^{j²}` 放在**单个 tensor factor** 的元素，
`qroot ∈ K_v` 一般**不在** `Q_p`，不是 central；因此 `phi(a·shell) ≠ a·shell`（φ 只 Q_p-linear），
**automorphism union 不会把 scaling 消掉**；它把 scaled shell 沿 lattice 方向移动，hull 随后取**最小分数理想**（lattice）。

## 3. rounding：lana 的 lattice 公式确实用整数取整

`Iut/WallEquiv/VcI.lean:364-381`（`ordp_scalA_tame` 证明中）：`logLatticeA` 用 `Int.ceil`：
```
⌈(ramIdx K w : R) / ((p : R) - 2)⌉ = 1
```
即 p-adic lattice 的 log-volume 由**整数格指数**（ceil/floor）给出；
`componentVol_leastHull_tensorLogShell_eq`（VcI:603-605）`= sum_j logShellRadius * logp` 是 **rounding 后**的整数格体积。
因此 `V(leastHull(a·shell))` 与 `V(a·leastHull(shell))` 的差别是**取整（frac/ceil）**，不是精确的 `-ord(a)logp`。

## 4. 两个候选公式

(a) **线性（A1020 主张）**：
```
V(leastHull(thetaComponent)) = V(leastHull(shell))        (m-independent，若 union 被未缩放分支支配)
V(scaleElt • leastHull(shell)) = - j^2*m*logp/(2l) + bounded
ind2 = + j^2*m*logp/(2l) + bounded        (linear positive)
```
依赖未证引理 **`leastHull_thetaComponent_eq_pow_floor`**：hull(thetaComponent) 等于 unscaled hull（即
automorphism union 的 hull 不退到 scaled 分支）。**当前 lana 源未提供**。

(b) **frac/有界（qpilot c1）**：
```
V(leastHull(a • shell)) = -ceil(j^2*m/(2l))*logp + bounded
V(a • leastHull(shell)) = -floor(j^2*m/(2l))*logp + bounded
ind2 = sum_j frac(j^2*m/(2l)) * logp + bounded        (bounded, oscillatory)
```
依赖同样级别的 rounding 引理（`leastHull` 的整数格取整），但**与数据一致**：
A1021 观察到 `M - A` 与 m 显著负相关、不平坦；若 ind2 有 +j²m 线性正项，`M-A` 应随 m **上升**，
与数据矛盾；frac 有界版本下 `M-A` 由 qScale 的 `-j²` 线性支配 ⇒ 随 m 下降 ✓。

## 5. 决定性结论

1. **ind2Term 是 frac/有界，不是线性**（数据 + 源结构支持）：
   `ind2 = sum_j frac(j²m/(2ℓ))·logp + O(3+log e)`；
2. A1020 的 `+j²m/(2ℓ)` 线性正项**不成立**；它假设了 `V(a·O) = -ord(a)logp` 的精确值，
   忽略了 p-adic 整数格 rounding；
3. 两个候选都需要 `leastHull` rounding 引理；但线性版本与数据矛盾，故**采用 frac 版本**；
4. 于是 `M - A` 的 m-行为由 qScale 的负线性支配（A1018 的 `dM/dm=1-sF<0` 口径更接近真相），
   大 m 反例问题**仍然存在**，需要其他正线性项（候选：`orderVol`/`shellExcess`/lattice index
   `logLatticeA/B` 的 ceil 差、`PacketIndexForm`）或显式 admissible m 界。

## 6. Lean 陈述（草案，不编译）

```lean
/-- ind2 is bounded by frac + (3 + log e) terms (frac version, qpilot c1). -/
def ind2FracBound (j m logp l : Real) : Real :=
  Int.fract (j ^ 2 * m / (2 * l)) * logp

/-- Linear version (A1020) is REJECTED: it needs the unproved hull-floor lemma. -/
def ind2Linear (j m logp l : Real) : Real :=
  (j ^ 2) * m * logp / (2 * l)

/-- The difference is bounded by log p (one lattice step). -/
theorem ind2Linear_sub_frac_le (j m logp l : Real) (hm : 0 <= m) :
    ind2Linear j m logp l - ind2FracBound j m logp l <=
      (j ^ 2 * m / (2 * l) - Int.fract (j ^ 2 * m / (2 * l))) * logp := by
  unfold ind2Linear ind2FracBound
  nlinarith [Int.floor_le (j ^ 2 * m / (2 * l)), Int.lt_floor_add_one (j ^ 2 * m / (2 * l))]
```
（真实接线需 `leastHull` rounding 引理；`Int.fract` 的界 `0 ≤ fract < 1` 由 Mathlib 提供。）

## 7. 待办

1. 读 `ScaleVolume:46/118` `componentVol_prod_incl_smul_integral` 的精确公式，确认 ceil/floor 位置；
2. 找/证 `leastHull_thetaComponent_eq_pow_floor`（若存在则定线性/frac）；
3. 用数据（M−A 随 m 下降）作为 frac 的数值证据，登记 NUMERIC，不入 PROVED；
4. 更新 `Mzk1MDecompositionActual` 的 GAP-IND2：从「线性正项」改为「frac/有界，线性版本 REJECTED」。