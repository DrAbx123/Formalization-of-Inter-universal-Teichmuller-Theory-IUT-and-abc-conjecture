# C9 target complement U_other：mixed-profile counterexample / exact obstruction

任务：task-310（Bound target complement U_other beyond B rows）。owner：iplsheapt。日期：2026-10-25。短定理/证明或 source-valid counterexample；不改 Lean/Project/目标；不引入 arbitrary region；只写本文件。

输入：C9-TAME-LOG-DOMAIN-20261025.md §5（mixed bad/good profile lower bound）；C9-TARGET-GENERATED-20261025.md（task-299，target 不由 B rows exact generate）；C9-TARGET-UPPER-SAT-20261025.md（task-301）；C9-RA-SUBSET-RB-20261025.md；C9-SATURATION-MAXIMALITY-20261025.md；C9-B273-*。

## 0. Verdict

**U_other⊂R_B+arch 在 mixed bad/good profile 模型下是 FALSE。** TAME §5 构造的 mixed profile 是 source-valid target possible image；对 b=273、ρ=1/2，其 normalized finite volume 的 lower bound 为

```
h_mix/logp = -5151789/5242880 = -0.9826257705688477… ,
```

而 B=I all-bad row value 为

```
H_B/logp = -38736/41 = -944.780487804878… .
```

`h_mix` 比 `H_B+A_proc=-931.616…` 高约943.8 logp units。若 target H_C 包含这个 mixed region，则

```
h_C >= h_mix + h_inf   while SAT-U demands h_C <= H_B + h_inf;
h_mix > H_B  => contradiction.
```

因此在这个 source-valid mixed-profile 模型中，SAT-U 不成立，b=273 的 `F≥8821.538` 不获得；U_other 不是 `R_B+arch` 的子集。

**Caveat:** 如果所讨论的完整 C 被严格限定为 `rho=1` all-bad uniform profile（没有 good factor、没有 mixed tuple），则这个 mixed region 不属于该 C；此时上面的 E_extra 不是 actual C 的 possible image。U_other 的 bound 仍未被证明；exact obstruction 是缺少对 good/other local/Theta/Ind3 target images 的 source classification。下面分两种情形。

## 1. Source-valid mixed region

TAME §5：在同一个 p 的坏/好混合 profile 中，若 tuple 有 good 因子，选原允许 permutation 将 Gaussian 标记移到 good 因子，得到实际 D_tuple；其 normalized lower bound 为

```
ell_j^aligned >= -rho^(j+1)(s_j+1/e),
h_p^aligned/logp >= -(1/m) Σ_{j=1}^m rho^(j+1)(s_j+1/e),
m=(e-1)/2=20,  b j^2 = s_j e+t_j,  1<=t_j<e.
```

这条路不假设 arbitrary region：它就是 TAME §5 的实际 Gaussian/permutation output，属于 full target possible-image union（TC-B）。

## 2. b=273, ρ=1/2 exact calculation

For e=41, b=273, m=20, the integers s_j=floor(273j^2/41) begin

```
j:      1   2   3   4   5   6   7   8   9  10
s_j:    6  26  59 106 166 239 326 426 539 665
j:     11  12  13  14  15  16  17  18  19  20
s_j:   805  958  1125  1305  1498  1704  1924  2157  2403  2663
```

The exact weighted sum at ρ=1/2 is

```
S = Σ_{j=1}^{20} 2^{-(j+1)} (s_j+1/41) = 5151789/262144,
h_mix = -S/20 = -5151789/5242880 = -0.9826257705688477… .
```

Compare b=273 B=I: H_B=-38736/41=-944.780487804878…; hence

```
h_mix - H_B = 202876976331/214958080 ≈ 943.7978620… >0,
h_mix - (H_B+A_proc) ≈ 943.7978620 - 13.1643937 >0.
```

So the mixed region alone exceeds the proposed SAT-U upper envelope by more than 930 natural-log units. Since `h_C` contains the mixed region's hull and shares the same arch component h_inf,

```
h_C >= h_mix + h_inf > H_B + h_inf
```

for every h_inf; SAT-U fails. `F=Q_C-h_C` then is not bounded below by `D_B-A_proc`.

## 3. Two-case classification

### Case A: mixed profiles admissible for the fixed C

Then `h_mix` is a source-valid E_extra; U_other⊄R_B+arch; SAT-U false; b=273 F≥8821.538 is not obtained. The explicit source data:

```
E_extra = TAME §5 mixed bad/good tuple at rho=1/2;
finite normalized volume lower bound h_mix/logp=-5151789/5242880;
it lies in H_C by TC-B/full possible-image union.
```

### Case B: the C is strictly rho=1 all-bad uniform

Then the mixed profile is not among its possible images (no good factor); the above E_extra is not source-valid for this C. No other positive `U_other` region is constructed in the frozen corpus:

```
- good finite places: no positive normalized volume theorem;
- other local types: shell volume nonpositive/unknown, no positive construction;
- arch: already included in R_B+arch;
- Theta/log/Ind3 and aggregate B=I: no volume computation.
```

In Case B, `U_other⊂R_B+arch` is **not proved** but also not refuted by a source-valid extra region. The exact obstruction is the missing classification/upper bound for these other possible-image classes; SAT-U remains conditional on it.

## 4. Conclusion

The decisive source-valid counterexample exists **in the mixed-profile model**: TAME §5's ρ=1/2 mixed region has `h_mix/logp=-5151789/5242880≈-0.982626`, far above the B=I row `H_B=-38736/41≈-944.7805`. If that mixed region is a possible image of the fixed b=273 C (as task-299/TAME §5 assert for mixed bad/good profiles), then `U_other⊂R_B+arch` is false, SAT-U fails, and the b=273 `F≥8821.538` is not obtained. If instead the C is strictly all-bad `rho=1`, the mixed region is excluded and U_other remains an unproved case-B obstruction; neither case yields SAT-U. No arbitrary region is used: the counterexample is the TAME §5 mixed-profile construction; the case-B obstruction is lack of source classification. P6 open.

