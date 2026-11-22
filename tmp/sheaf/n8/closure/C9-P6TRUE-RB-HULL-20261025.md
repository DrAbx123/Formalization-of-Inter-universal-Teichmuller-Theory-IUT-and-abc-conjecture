# C9 P6-true b=3：R_B ⊂ H_C 的证明/障碍

任务：task-350（P6-true b=3: prove R_B subset H_C）。owner：iplsheapt。日期：2026-10-25。短定理/证明或 exact obstruction；不改 Lean/Project/目标；不引入 arbitrary region；只写本文件。No mixed/E3。

输入：C9-BI-REGION-CONSTRUCTION-20261025.md（R_B 显式 row region）；C9-BI-REGION-HULL-20261025.md（task-272）；C9-TAME-LOG-DOMAIN-20261025.md §6；C9-IND1-GLOBAL（TC-B/full possible images）；C9-UNIFORM-B3-P6（H1-H4）；C9-RA-SUBSET-RB/REGION-INCLUSION；C9-TC-EQUALITY。

## 0. Verdict

**R_B⊂H_C 不是独立的几何估计；它是 TC-B target-saturation 的语义内容。** 精确地：

```
H_C := Hull( all actual possible images );
if R_B is an actual possible image and TC-B holds, then R_B⊂H_C by definition.
```

当前 frozen source 不提供两个前提：

```
(S1) B=I branch actual: a real source generator/barGamma element moving l=O_K/J,
     producing the B=I row lattice as an actual possible image;
(S2) actual TC-B target hull H_C and the fixed Theta/BPS/gluing transport.
```

因此 **无条件的 R_B⊂H_C 没有证明**；得到的是 conditional semantic theorem + exact obstruction。No arbitrary target enlargement is allowed.

Under S1/S2 and the normalized-volume formula, `h_C≥H_B+h_inf`. For b=3 B=I, `H_B=9/41 logp`, `Q_p=−3/41 logp`; hence

```
h_C≥H_B+h_inf;   P6 (h_C≥Q_p) iff h_inf≥−(12/41)logp=−S_3.
```

So R_B⊂H_C gives P6 only together with the separate arch lower bound `h_inf≥−S_3`; it is not by itself P6-true.

## 1. Explicit R_B and H_C semantics

b=3 uniform rho=1, row j, r=j+1:

```
s_j=floor(3j^2/41),   R_B,j=Hull(p^{s_j-r+1}J^{⊗r}),
R_B=⋃_{j=1}^{20} T(R_B,j),   weight 1/20,
h_B=(1/20)Σ_j[-s_j+j-(j+1)/41]·logp = 9/41 logp.
```

H_C is defined by IUT III Cor3.12/TC-B as the normalized holomorphic hull of the union of **actual** possible images under Ind1/Ind2/Ind3. The semantic implication is

```
R_B actual possible image  +  TC-B  ⇒  R_B⊂H_C.
```

No inequality or new geometric construction is needed; conversely, without the actual image, asserting R_B⊂H_C would be an enlargement of the target, not a theorem.

## 2. Conditional theorem and P6

**Theorem 2.1 (conditional R_B inclusion).** Assume (S1) R_B is produced by an actual B=I source/barGamma configuration, (S2) TC-B holds for the actual complete C, and (S3) the transported normalized volume of R_B is H_B. Then

```
R_B⊂H_C,   h_C≥H_B+h_inf.
```

**Corollary 2.2.** If additionally `h_inf≥−S_3`, then `h_C≥Q_p`, i.e. b=3 P6 holds for that C. Proof: H_B−S_3=9/41−12/41=−3/41. QED

The corollary is the P6-true b=3 route. It is conditional on S1-S3 **and** the arch lower bound. It is independent of the b=273 upper-side question (different sign).

## 3. Exact obstruction

None of the following is in the frozen source:

```
(O1) actual B=I generator/barGamma moving l=O_K/J;
(O2) actual complete C, TC-B target H_C, Theta/BPS/gluing transport T;
(O3) normalized-volume identity for the transported R_B;
(O4) arch lower bound h_inf≥−S_3 (IV only gives upper A_proc).
```

Consequences:

- If actual B branch is B=O_K (natural trace alignment), R_B is not an actual image; including it in H_C changes the target. No arbitrary enlargement allowed.
- If B=I is not constructed, R_B is only a conditional lattice formula; S1 missing.
- If h_inf<−S_3, even a legitimate R_B inclusion gives h_C≥H_B+h_inf<Q_p: P6 not decided; the B=I corridor needs the arch lower bound.
- No source-valid counterexample to R_B⊂H_C is known: if S1/S2 hold, inclusion is definitional. The failure is non-realization, not a geometric contradiction.

## 4. What would prove R_B⊂H_C unconditionally

One would need **both**:

```
(A) a source theorem that the barGamma/B=I branch is actually realized (kappa∈[1,40] or equivalent);
(B) an actual TC-B target-container theorem (C_K/C_F/V/ε + Theta/BPS/gluing) showing the full possible-image union contains the transported R_B.
```

Neither is a consequence of TAME §6 alone: §6 classifies the B=O_K/B=I row subfamily but is not an upper/global target theorem. The B=I branch itself is conditional/type-gapped; H_A-full/B branch remain open.

## 5. Classification

| item | status |
|---|---|
| R_B explicit row formula / H_B=9/41 | CONDITIONAL source formula |
| R_B⊂H_C | CONDITIONAL on actual B=I + TC-B; definitional |
| h_C≥H_B+h_inf | CONDITIONAL on inclusion+volume |
| b=3 P6 under h_inf≥−S3 | CONDITIONAL |
| actual B=I | NOT PROVED |
| actual TC-B/H_C | NOT PROVED |
| h_inf≥−S3 | NOT PROVED |
| unconditional R_B⊂H_C / P6-true b=3 | NOT PROVED |

## 6. Conclusion

The b=3 B=I region R_B is contained in the target hull H_C **by definition of TC-B**, provided R_B is an actual possible image and TC-B is realized. That is the only correct proof; it is not an independent geometric estimate. The frozen source does not construct the actual B=I generator, the actual H_C/TC-B, or the arch lower bound h_inf≥−S_3. Therefore R_B⊂H_C and the b=3 P6-true conclusion are conditional. No mixed/E3, no arbitrary region, no Lean/Project edits; P6 open.

