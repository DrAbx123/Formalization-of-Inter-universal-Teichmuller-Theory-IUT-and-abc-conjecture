# C9 adjudication：H_A-full 的 W=ker Tr 与 J=m

任务：task-203（adjudicate task-196 vs task-200 H_A-full conflict）。owner：iplsheapt。日期：2026-10-25。自然语言/精确局部代数裁决；不改 Lean/Project/目标；不新增 attack；只写本文件。

裁决对象：

- task-195/C9-HAFULL-ALPHA1-20261025.md，SHA256 BA8459C4500B8E73ACFA12A3C20431C5FDF8ED1AF077DDD453F5D3C4F2E6A43B
- task-196/C9-AUDIT-HAFULL-LITE-20261025.md，SHA256 EF755618B74DC45913A6DD148E1E60ABC97CB6C4188748AC6F907EF9305FF223
- task-200/C9-AUDIT-HAFULL-ALPHA1-20261025.md，SHA256 8B63FF614DE6E3E041C850C5AB829D60EE376A7EF622176A9760F97D0A9D80A6
- 背景：C9-HAFULL-CONSTRUCT-20261025.md，SHA256 C02D4A24CD201AD6F0FC2D5E308772F943AE29C911058F40ED19A2C8D7BA6878

## 0. Binding verdict

1. `W := ker Tr_{K/Q_p}` 是 **K 的 Q_p-超平面**（dim_Qp W=40），不是 Z_p-lattice。
2. `J=m=πO_K` 是 O_K 的极大理想，是 **rank 41 的 Z_p-lattice**；`O_K=Z_p+J`。
3. `K=Q_p·1 ⊕ W` 作为 **Q_p-vector space** 正确；`Tr(1)=41` 是 p-adic unit。
4. `W∩J = Z_p-span(π,π²,...,π^40)`（rank40），但 **`W⊄J`**。反例：`π/p ∈ W`，但 `π/p ∉ m`。
5. 因此 task-195 的步骤 `w(α)∈W⊆J` 是 **错的**；`α_+(1)=λ1+w` 的 `w` 不一定在 J，`α_+(1)∈O_K` 未被证明；所有下游 O_K-preservation、`B=O_K`、`B=I` exclusion **无效**。
6. **task-196 audit 的核心裁决正确**；**task-200 audit 错误**，它把 `W=ker Tr` 写成 `Z_p-span(π,...,π^40)⊆J`，混淆了 Q_p-span 与 Z_p-lattice。
7. H_A-full 仍未证明；full Out 的 `B=O_K` 与 `B=I` 都未决定；B=I 未被排除。Gamma_0/field subgroup 的 `B=O_K` 仍是条件性子群结果。

## 1. 定义与精确局部代数

取 K/Q_p tame totally ramified cyclic，e=41，p=12301，`K=Q_p(π)`，`π^41=p u`，u∈Z_p^×，f=1。

```
O_K = Z_p[π] = Z_p + Z_pπ + ... + Z_pπ^40;
m = πO_K = Z_pπ + Z_pπ² + ... + Z_pπ^40 + Z_pπ^41 (π^41=p u);
J = log(O_K^×) = m;   I = p^{-1}J;   l=O_K/J=span_Fp(1).
```

Trace table：

```
Tr(1)=41;   Tr(π^a)=0  (1≤a≤40).
```

因为 p=12301∤41，Tr 非零。于是

```
W := ker Tr = Q_p-span(π,π²,...,π^40),  dim_Qp W=40.
```

W 是 Q_p-vector space，不是 Z_p-module lattice；它包含 `π/p` 等非整元素。

`J=m` 的 Z_p-basis 可取 `π,π²,...,π^40,π^41=p u`，rank41；`W∩J` 由 trace0 的 m-元素组成：

```
W∩J = Z_p-span(π,π²,...,π^40),  rank 40.
```

`p u=π^41` 的 trace `41 p u ≠0`，所以不在 W；W 的 Q_p-span 还包含 `p^{-1}π` 等，后者不属于 m。

## 2. task-196 与 task-200 的对错

### 2.1 task-196 audit（正确）

task-196 明确写：

- `W=ker Tr` 是 Q_p-hyperplane dim40；
- `J=m` 是 Z_p-lattice rank41；
- `W⊄J`；`W∩J=Z_p-span(π,...,π^40)`；
- task-195/E24 的 `W⊆J` 步骤不成立，因此 α_+(1) 不一定在 O_K，H_A-full 无效。

这些与 §1 的精确计算完全一致；task-196 是正确裁决。

### 2.2 task-200 audit（错误）

task-200 的 fatal step 是

```
W = ker Tr = span(π,...,π^40) ⊆ J.
```

如果 `span` 是 Z_p-span，则它等于 W∩J，**不是** ker Tr（W 还含 `p^{-1}π` 等）；如果 `span` 是 Q_p-span，则 W 不是 J 的子集。两种读法都错。

task-200 随后用 `w∈W⊆J` 推出 `α_+(1)=λ1+w∈O_K`，再推出 `α_+(O_K)⊆O_K` 和 `B=O_K`；这些步骤均继承同一错误。其 λ/trace 标量部分本身正确，但不能证明 α_+(1) 的整性；`w` 在 W 中可能无界。

### 2.3 task-195（无效 as written）

task-195 的核心推导：

```
α_+(1)=λ(α)1+w(α),  w(α)∈W⊆J  ⇒ α_+(1)∈Z_p+J=O_K.
```

第一行是 Q_p-线性分解（正确）；第二行的 `w∈J` 错误。因此 `α_+(1)∈O_K`、`α_+(O_K)=O_K`、`B=O_K`、`B=I excluded` 均未证明。task-195 的 trace/lambda/compactness 部分可作为**条件性 partial**：若另有 `w∈J` 或 α_+(1) 整性，才可继续；目前没有。

## 3. 对 H_A-full 与 B 分支的 binding verdict

### 3.1 H_A-full

- **H_A-lite**（full Out 保 J、I，F_p-action on I/J）仍是条件性 valid（依赖 Kondo/AbsTopIII interface）；
- **H_A-full**（full Out 保 O_K）**未证明**；α_+(1) 的 additive integral lift 缺失；
- Gamma_0=Stab(O_K) open finite index，`B_Γ0=O_K` 仍 conditional valid；
- Aut(K) 的 diagonal action 仍 actual：`B_Aut(K)=O_K`，不产生 B=I；
- full Out 的 `B=O_K` 与 `B=I` 均未决定；B=I 未被排除。

### 3.2 B=O_K / B=I

```
B_Γ0=O_K       (conditional subgroup result)  -- valid;
B_Aut(K)=O_K   (actual local field subgroup)  -- valid;
B_full=O_K     -- NOT proved;
B_full=I       -- NOT excluded;
B_full branch  -- undetermined.
```

因此：

- task-200 的 “B=O_K for full Out、B=I excluded” **无效**；
- task-196 的 “full H_A-full/B remain unconstructed；B=I not excluded” **binding**；
- conditional b=3 B=I 的 9/41 surplus 仍只是 conditional，不得作为 actual；B=O_K 的 408/41 也只是 conditional finite value，不能宣称 full branch selected。

## 4. 错误归因

| 文件 | 核心断言 | 裁决 |
|---|---|---|
| task-196 C9-AUDIT-HAFULL-LITE | W Q_p-hyperplane; J lattice; W⊄J; W∩J=Z_p-span; task-195 invalid | **CORRECT / binding** |
| task-200 C9-AUDIT-HAFULL-ALPHA1 | W=span(π..π40)⊆J; task-195 passes; B=O_K; B=I excluded | **ERROR** at W⊆J; downstream invalid |
| task-195 C9-HAFULL-ALPHA1 | α_+(1)=λ1+w, w∈W⊆J ⇒ O_K-preservation | **INVALID as written** at w∈J |

## 5. actual / conditional / missing

### Actual / exact local

- K/Q_p tame e=41, f=1, π^41=p u; O_K,m,J,I,l definitions；
- Tr table; W=Q_p-span(π..π40), dim40; W∩J=Z_p-span(π..π40);
- `π/p∈W` but `π/p∉J`; `K=Q_p1⊕W`; `O_K=Z_p+J`.

### Conditional / valid

- H_A-lite 的 J/I action（Kondo/AbsTopIII interface）；
- Gamma_0 open finite index, B_Γ0=O_K；
- Aut(K) diagonal/B_Aut(K)=O_K；
- task-195 的 λ(α)∈Z_p^× 与 α_+(1)=λ1+w 的 Q_p 分解（但不含 w∈J）。

### Missing / invalid

- α_+(1) 的 integral lift / w∈J；H_A-full full Out；
- full B=O_K/B=I decision；Gamma_0=Out；
- explicit full generator matrices/lambda/w；
- 任何完整 C 或 target conclusion。

## 6. 结论

Binding verdict：**task-196 正确，task-200 错误，task-195 invalid as written**。精确原因是：`W=ker Tr` 是 Q_p-vector space（dim40），`J=m` 是 rank41 Z_p-lattice；`W∩J` 只有 `Z_p-span(π,...,π^40)`。所以 `w∈W` 不蕴含 `w∈J`，α_+(1) 的 additive integrality 未证，H_A-full、full B=O_K、B=I exclusion 均不成立。Gamma_0/Aut(K) 的 B=O_K 仍是条件性/子群结果；full B 分支 undetermined，P6 open。

本文件只做裁决；没有新增 attack，没有 Lean/Project edits，target_accepted=false。

