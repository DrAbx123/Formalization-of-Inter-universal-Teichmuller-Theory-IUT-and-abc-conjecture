# C9 target-upper saturation：H_C ⊂ R_B+arch / h_C≤H_B+h_inf

任务：task-301（Final U attack: target-upper row saturation）。owner：iplsheapt。日期：2026-10-25。短定理/证明或 countermodel；不改 Lean/Project/目标；不引入 arbitrary enlargement；只写本文件。

输入：C9-RA-SUBSET-RB-20261025.md（R_A⊂R_B proved）；C9-REGION-INCLUSION-20261025.md；C9-SATURATION-UPPER-20261025.md（task-290）；C9-TAME-LOG-DOMAIN-20261025.md §6；C9-TC-EQUALITY-20261025.md（C1 lower）；C9-IND1-GLOBAL-20261025.md（TC-B/full Ind1）。

## 0. Verdict

**SAT-U（global `H_C⊂R_B+arch` / `h_C≤H_B+h_inf`）没有证明；得到的是精确 obstruction + row-only conditional theorem。**

已证（task-291）：

```
R_A⊂R_B,   R_B=Hull(L_B),   L_B=p^{s-r+1}J^{⊗r}.
```

若 target 只由固定的 all-bad r-tuple row subfamily 生成，则

```
H_C^{row}=Hull(R_A∪R_B)=R_B,   h_C^{row}=H_B,
```

此时 SAT-U 对 **row part** 成立，且 `h_C≤H_B+h_inf`。但 TAME §6 明确说这个 row classification 只针对所列 actual subfamily，不是整个 C 的 log/Θ/∞ 输出族的上界。Full `H_C` 还可能含其他 local types、good places、Theta/log/indeterminacy 输出；没有 theorem `H_C⊂R_B`。因此 global SAT-U 不成立/不可证；b=273 的 `F≥8821` 仍然只在 SAT-U 或 row-only target 的额外假设下成立。

## 1. Row-only saturation theorem (conditional)

For a fixed all-bad r-tuple, TAME §6 classifies the actual subfamily additive hull as `R_A` or `R_B`, and task-291 proves `R_A⊂R_B`. Therefore

```
H_C^{row}=Hull(R_A∪R_B)=R_B.
```

With arch component `h_inf`, the row target satisfies

```
h_C^{row} ≤ H_B + h_inf(C),
h_inf≤A_proc=13.164393687… .
```

This is a genuine conditional upper bound for the row subfamily, not the global target. It uses `R_A⊂R_B` and the row classification, no arbitrary region.

## 2. Why global SAT-U does not follow

Full target H_C by TC-B is the hull of the **full possible-image family**:

```
H_C = Hull( U_row ∪ U_other ),
```

where `U_row` is TAME §6's all-bad row subfamily and `U_other` contains the remaining possible images (other local types, good places, aggregate B=I, Theta/log/Ind3 branches, arch/∞ regions). TAME §6 explicitly disclaims being an upper bound for the entire C output family. TC-B is a lower/saturation statement: it says `U_row⊂H_C`, not `H_C⊂U_row`.

For `H_C⊂R_B+arch`, one needs

```
(SAT-U-row) U_row⊂R_B+arch      (true for the row part);
(SAT-U-other) U_other⊂R_B+arch   (missing);
(SAT-U-union) Hull(U_row∪U_other)⊂R_B+arch (missing).
```

No source theorem supplies SAT-U-other/union. In particular, TAME's claim that repeated same-type automorphisms saturate **inside the listed subfamily** does not bound other output branches.

## 3. Exact countermodel to global SAT-U

Take a target configuration whose full possible-image family is

```
U = U_row ∪ U_other,
```

with `U_row` as the TAME row subfamily (so `R_A⊂R_B` and all row statements hold) and `U_other` containing one actual possible image `E_extra` whose hull is not contained in `R_B+arch`. Such other possible images are exactly the branches TAME §6 disclaims; TC-B saturation includes them. Then

```
H_C = Hull(U) ⊃ Hull(U_row ∪ E_extra) ⊄ R_B+arch,
```

so `h_C≤H_B+h_inf` fails. This is a **countermodel to SAT-U as a consequence of TC-B/full Ind1/TAME §6**, not an arbitrary enlargement: `E_extra` is a possible image of the full output family (other local type/good/Theta/log/Ind3 branch); the source does not provide an upper bound on it. The row-only inclusion remains true because it only concerns `U_row`.

**Explicit obstruction data:** a complete C/BPS/Theta datum realizing `E_extra` and its normalized volume is missing. The countermodel shows that no proof can derive SAT-U from the row classification/TC-B alone; additional target-upper data are required.

## 4. Consequence for b=273

The conditional theorem remains:

```
If SAT-U: H_C⊂R_B+arch, then
h_C≤H_B+h_inf≤H_B+A_proc,
F=Q_C-h_C≥D_B-A_proc
 = (38463/41)log12301 - 11.5logπ
 = 8834.703284644… - 13.164393687…
 = 8821.538890956… >0.
```

This is the b=273 counterexample, conditional on SAT-U (or row-only target). Without SAT-U, the full H_C may be larger; C1 only gives `h_C≥H_B+h_inf`, hence `F≤D_B-h_inf` (upper bound on F, not a lower bound). No b=273 counterexample follows from TC-B/row inclusion alone.

For b=3, row-only SAT gives analogous upper consequences; the global b=3 corridor still requires the same target-upper data.

## 5. Classification

| item | status |
|---|---|
| R_A⊂R_B | PROVED (task-291) |
| row-only H_C^row=R_B / h_C^row≤H_B+h_inf | PROVED conditional on row-only target |
| global H_C⊂R_B+arch | NOT PROVED; countermodel |
| TAME §6 is global upper bound | FALSE (explicitly disclaimed) |
| SAT-U + arch ⇒ b=273 F≥8821 | PROVED conditional |
| b=273 unconditional counterexample | NOT OBTAINED |
| extra U_other volume bound | MISSING |

## 6. Conclusion

R_A⊂R_B proves the row-hull ordering and gives a **row-only** upper bound `H_C^row=R_B`. It does **not** prove the global target-upper saturation `H_C⊂R_B+arch`: TAME §6 classifies only the actual row subfamily and explicitly excludes the rest of the C output family; TC-B is lower-bound/saturation, not an upper bound. A countermodel with one extra full-possible-image branch outside R_B violates SAT-U while preserving all row statements. Therefore SAT-U is a conditional sufficient condition, not a source theorem; b=273 F≥8821 remains conditional. No arbitrary enlargement; no Lean/Project edits; P6 open.

