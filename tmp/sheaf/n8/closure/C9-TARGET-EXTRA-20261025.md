# C9 target extra volume >=8808? 正 saturation 的定理/障碍

任务：task-276（NL theorem: target extra volume >=8808 or obstruction）。owner：iplsheapt。日期：2026-10-25。短定理/证明；不改 Lean/Project/目标；不引入 arbitrary enlargement；只写本文件。

输入：C9-P6-NOGO-20261025.md（task-256，E47 convention）；C9-TC-EQUALITY-20261025.md（task-266，C1 只有 lower）；C9-TARGET-POSITIVE-20261025.md（task-271，已知 canonical regions）；C9-IND1-GLOBAL-20261025.md（TC-B/full Ind1）；C9-ARCH-HULL-20261025.md。

## 0. Verdict

**没有构造出 b=273 所需的 canonical target region；得到的是 exact obstruction。**

C1 只给

```
h_C >= H_sel + h_inf,   H_sel = sum_bad alpha_p H_p^Sp log p.
```

从 selected region 到 P6 还需要的 target extra 是

```
R_req = Q_C - (H_sel+h_inf) = D_C - h_inf.
```

在 `h_inf<=A_proc=11.5logπ=13.1643936873` 下，最小所需为

```
B=O_K: R_req,min = D_A - A_proc = 8918.010184916…;
B=I:   R_req,min = D_B - A_proc = 8821.538890957… .
```

当前可构造的 canonical target extra 最多是 B=I sibling；其 target-region volume 为

```
Delta_B = (420/41) log 12301 = 96.471293959… .
```

Arch cap `A_proc` 不是一个额外的 target region，而是 `h_inf` 的上界；若按 task 要求的“combined canonical extra”把它也计入，则

```
Delta_B + A_proc = 109.635687646… .
```

即使采用这个偏乐观的 combined 上界，仍远小于所需 8918.010/8821.539；对应 gap 至少

```
B=O_K: 8918.010184916 - 109.635687646 = 8808.374497270…;
B=I:   8821.538890957 - 109.635687646 = 8711.903203311… .
```

所以 **没有 canonical region with volume>=8808**；精确障碍是缺少一个 source theorem（或 target upper bound）构造出 `R_req`。TC-B 本身是 lower-bound/saturation 语义，不能排除未知大区域；不能把未知区域当作已构造。

## 1. Exact required extra

E47 data:

```
Q_p = (-273/41) log p;
H_A = (-39156/41) log p  (B=O_K);
H_B = (-38736/41) log p  (B=I);
D_A = Q_p-H_A = (38883/41) log p = 8931.174578603…;
D_B = Q_p-H_B = (38463/41) log p = 8834.703284644…;
A_proc = 13.164393687…;
Delta_B = H_B-H_A = (420/41) log p = 96.471293959… .
```

Because `h_inf<=A_proc`, for any target-compatible h_inf:

```
R_req = D_C - h_inf >= D_C - A_proc.
```

Thus a **sufficient** canonical region would need volume at least `D_C-A_proc`; the task's “at least 8918 (B=O_K) or at least 8834 (B=I)” uses D_C before the arch cap for B=I. We state both exactly:

| branch | D_C before arch | R_req,min after A_proc |
|---|---:|---:|
| B=O_K | 8931.174578603 | 8918.010184916 |
| B=I | 8834.703284644 | 8821.538890957 |

## 2. Canonical extra available

The only quantified canonical regions are:

```
(A) B=I sibling local region: volume Delta_B=96.471293959;
(B) arch IV cap: h_inf<=A_proc=13.164393687 (cap, not region);
(C) full Ind1 / factor permutations / BPS/Theta gluing: no volume computation.
```

TC-B says `H_C` is the hull of the full possible-image family; this makes `H_C` **larger** than the selected subfamily, but it does not give a numeric volume for the complement. The B=I sibling is the only quantified next region, and its increment is b-independent (`Delta_B=(420/41)logp`), so it cannot scale to cover the b=273 deficit.

## 3. Obstruction theorem

**Theorem 3.1 (exact target-extra obstruction).** Under the current constructed target-saturation data (selected source subfamily + B=I sibling + arch cap), there is no canonical region of normalized volume `>=8808`, and no such region of volume `>=R_req` for b=273. Quantitatively:

```
region-only:  Delta_B=96.471293959;
optimistic combined: Delta_B+A_proc=109.635687646;
gaps to R_req,min:
  B=O_K: >=8808.374497270 (combined) or 8821.538890957 (region-only);
  B=I:   >=8711.903203311 (combined) or 8725.067596998 (region-only).
```

Proof: C1 baseline; exact arithmetic in §1-§2; monotonicity. The selected and B=I regions are the only quantified target extra; their total is `Delta_B=96.47`; the arch cap adds at most `A_proc` in a combined bookkeeping comparison, total109.64. Both are far below `8808` and below `R_req,min`. QED.

**Scope.** This is not a proof that the full possible-image family `H_C` cannot contain an unknown larger region. TC-B is a saturation/lower-bound statement: `H_C` contains the full possible-image hull; it gives no upper bound on its finite volume. The exact missing theorem is either:

```
(EXTRA) a canonical source possible-image region R with nu(R)>=R_req; or
(UPPER) an upper bound on the target complement showing no such region exists.
```

Neither is in the current corpus. An arbitrary enlargement of `H_C` is excluded.

## 4. b=3 comparison (why the B=I sibling can rescue only b=3)

For b=3 B=O_K, `D_3=(408/41)logp=93.714971275`; the B=I sibling increment is

```
Delta_B-D_3 = (420-408)/41 logp = (12/41)logp = S3 = 2.756322685 >0.
```

So if TC-B includes the B=I region and `h_inf>=-S3=-2.756322685`, then `h_C>=H_B+h_inf>=Q_p`; this is the conditional b=3 rescue. For b=273 the same fixed `Delta_B=96.47` is insufficient by more than 8808; the b-dependence of the finite deficit `D_273≈8931` cannot be matched by a b-independent sibling.

## 5. Proved / conditional / obstruction

Proved exact:

- R_req,min = 8918.010184916 (B=O_K) / 8821.538890957 (B=I);
- Delta_B=96.471293959; combined Delta_B+A_proc=109.635687646;
- gaps >=8808.374497 (B=O_K) / 8711.903203 (B=I);
- no constructed canonical region reaches 8808; b=3 conditional sibling rescue.

Conditional:

- B=I sibling is an actual target possible image / TC-B includes both branches;
- h_inf arch cap A_proc and target C3; actual h_inf; complete C/TC/CFTH;
- full Ind1/BPS/Theta-gluing region volume (not computed).

Missing/obstruction:

- canonical target region volume >=R_req (or >=8808);
- source theorem computing full possible-image complement volume;
- upper bound excluding such a region. TC-B alone cannot supply it.

## 6. Conclusion

The positive target saturation needed for b=273 is **not constructed**. The only canonical target-region extra is `Delta_B=96.471293959`; even adding the arch cap `A_proc=13.164393687` as a combined bookkeeping bound gives109.635687646, while the minimum required is8918.010/8821.539. The resulting gap is at least8808.374 in the optimistic combined accounting (larger in region-only accounting). This is an exact obstruction to the current constructions, not an impossibility proof for unknown `H_C`; the missing input is a canonical region of the required volume or a target upper bound. No arbitrary enlargement; no Lean/Project edits; P6 open.

