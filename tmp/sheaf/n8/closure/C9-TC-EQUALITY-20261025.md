# C9 TC-C 方向：h_C 与 sum h_p+h_inf 的 equality / upper / lower

任务：task-266（TC-C direction/equality correction）。owner：iplsheapt。日期：2026-10-25。短定理/证明；不改 Lean/Project/目标；不引入 arbitrary volume；只写本文件。

输入：C9-IND1-GLOBAL-20261025.md（TC-A..H/TC-S；task-149）；C9-GLOBAL-ASSEMBLY-CORRECTED2-20261025.md（B1-B3）；C9-GLOBAL-ASSEMBLY-BINDING-20261025.md（binding C1/lower）；C9-P6-NOGO-20261025.md（task-256 b=273 no-go）；C9-ARCH-HULL-20261025.md。

## 0. Verdict

**TC-C 只给出 lower bound，不给出 equality，也不给出 upper bound。**

```
C1 (conditional, valid):   h_C >= sum_bad alpha_p H_p^Sp log p + h_inf(C).
Missing:                   h_C = sum...  或  h_C <= sum... .
```

因此 task-256 的 b=273 no-go **不能**从 TC-A..H/TC-S + C1 推出：它需要 `h_p=H_p^Sp` 的 exact 局部等式或 `h_C<=sum H_p^Sp+h_inf` 的 upper bound，而 TC/CFTH 没有这两条。b=273 no-go 只有加入一个**新的 TC-C-upper/equality theorem** 才能修复；该 theorem 当前缺失。

## 1. 术语与 C1

H_C 是 target possible images 的 holomorphic hull；h_C 是它的 normalized log-volume。CFTH/TC-S 的 C1 是

```
h_C >= sum_{p in S_bad} alpha_p H_p^Sp log p + h_inf(C),        (C1)
H_p^Sp = -(1/m0) sum_j (s_j+1/e) log p,   m0=(e-1)/2.
```

C1 的证明方向是**单调性**：H_p^Sp 来自实际 source subfamily 的局部 hull 下界；这些 source 区域被送入 target hull，故 target hull 的 volume 不小于它们的和，再加 archimedean 部分。它不声称 H_C 恰等于这个 subfamily hull。

## 2. 为什么 C1 是 lower

Target H_C 由**全部** possible images 的 union 的 hull 给出（IUT III Cor3.12/TC-B saturation）：

```
H_C = Hull( union_{Ind1/2/3} possible images ).
```

C1 使用的是其中 selected local/source subfamily `R_sel`：

```
R_sel subset union possible images  =>  Hull(R_sel) subset H_C
=>  nu(H_C) >= nu(Hull(R_sel)) = sum H_p^Sp + h_inf.
```

这是 volume monotonicity，方向是 `H_C >= R_sel`。没有任何一步给出 `H_C subset Hull(R_sel)`。

## 3. 为什么 equality/upper 不能从 TC 推出

TC-A..H/TC-S 的内容是：

| condition | content | direction |
|---|---|---|
| TC-A | source procession/β in Ind1 | source identity |
| TC-B | target saturation: H_C is hull of full possible-image family | H_C ⊃ selected subfamily; **larger** |
| TC-C | F preserves target hull and normalized volume | isometry/preservation, no equality of H_C with sum |
| TC-D | row/place/profile preserved | label containment |
| TC-E | Theta/gluing/q-class preserved | label containment |
| TC-F | log/Ind3 branch | branch compatibility |
| TC-G | n/infinity separate | scope condition |
| TC-H | Ism/Ind2 tracked | volume/indeterminacy bookkeeping |
| TC-S | corrected symplectic donor | source donor |

其中没有一条是 `H_C subset Hull(R_sel)` 或 `h_p=H_p^Sp`。TC-B 的 saturation 反而是**反向**：full possible-image family 比 selected subfamily 更大，所以只加强 lower bound。TC-C 的“normalized-volume preservation”是 F 的 isometry，不是 H_C 与局部 subfamily volume 的 equality。

**Exact obstruction (logical countermodel).** 在 C1 之外给 H_C 增加一个额外 possible-image region `E_extra`（体积 `ε>0`），并令 target hull 取 union 的 hull；所有 TC-A..H 的 containment/preservation 语义仍可满足（F 仍是 volume-preserving on its source region），但

```
h_C >= sum H_p^Sp + h_inf + ε  (if E_extra outside R_sel),
```

而 equality 与 upper bound 同时失败，C1 仍成立。这个 countermodel 不是 actual C，但它证明：**从 C1 + TC-C 的 volume-preservation 语义推不出 equality/upper**；需要额外的 reverse-inclusion/maximality 定理。

## 4. Exact TC-C direction

**Theorem TC-C-direction (conditional).** 在 CFTH/TC-S 与 C1 的实际 source subfamily 下：

```
(L) h_C >= sum_bad alpha_p H_p^Sp log p + h_inf(C)       [C1, valid]
(E) h_C = sum_bad alpha_p H_p^Sp log p + h_inf(C)       [not proved]
(U) h_C <= sum_bad alpha_p H_p^Sp log p + h_inf(C)      [not proved]
```

只有 (L) 是 TC-C/CFTH 的结论。 (E)/(U) 需要：

```
(EQ1) target hull 的 full possible-image family 恰等于 selected subfamily 的 hull；
(EQ2) 每个 local h_p 恰等于 H_p^Sp（不只是 lower bound）；
(EQ3) h_inf 是 exact target arch 值，而不是 upper container。
```

TC-A..H/TC-S 没有 (EQ1)-(EQ3)。

## 5. 对 task-256 b=273 no-go 的影响

Task-256 计算

```
F=Q_C-h_C = sum_p alpha_p(Q_p-h_p)-h_inf.
```

若只有 C1：`h_C >= sum H_p^Sp + h_inf`，代入得到

```
F <= sum_bad alpha_p(Q_p-H_p^Sp) - h_inf
  = D_C^Sp - h_inf,       （一个 upper bound on F）
```

这不是 `F>0` 的证明。要得到 `F>=D-h_inf`/`F>0`，必须用

```
h_C <= sum H_p^Sp + h_inf   (upper)  或 equality.
```

因此：

- b=273 no-go 作为 **TC/CFTH 定理**是 invalid（task-256 把 lower 当 equality）；
- 若额外假设 upper/equality，则 `F>=8931.1746-A_proc=8918.0102>0`（B=O_K）或 `F>=8834.7033-A_proc=8821.5389>0`（B=I），no-go 恢复；但这假设正是缺失的 TC-C-upper/equality；
- 没有 upper/equality 时，F 的符号未定；不能宣称 b=273 counterexample。

## 6. Classification

| item | status |
|---|---|
| C1: h_C >= Σ H_p^Sp+h_inf | **PROVED conditional (lower)** |
| TC-C gives equality | **NO / not in source** |
| TC-C gives upper h_C<=ΣH_p+h_inf | **NO / not in source** |
| TC-B saturation direction | full family larger; supports lower, not upper |
| TC-C volume preservation | isometry, not equality with Σ |
| EQ1/EQ2/EQ3 | MISSING |
| task-256 b=273 no-go | **INVALID as TC/CFTH theorem**; needs upper/equality hypothesis |
| conditional repair with upper/equality | valid conditional arithmetic |

## 7. Conclusion

TC-C 方向是 **lower bound**，不是 equality/upper。C1 的 monotonicity 只给 `h_C>=Σ H_p^Sp+h_inf`；TC-B 的 target saturation 使 full hull 只会更大，TC-C 的 volume preservation 是 F 的 isometry，不比较 H_C 与 selected subfamily。EQ1-EQ3（target hull = selected subfamily hull、local exact h_p、exact h_inf）均缺失。故：

```
TC gives LOWER only;
task-256 b=273 no-go cannot be repaired from TC alone;
an explicit upper/equality theorem is a new missing input.
```

No arbitrary volume equality; no Lean/Project edits; P6 open.

