# Independent audit: C9 archimedean normalization decision

Task: task-186. Auditor: qside. Date: 2026-10-25.
Stage: independent natural-language verification; no Lean/Project/target edits;
only this file written.

Audited document: `C9-NORMALIZATION-DECISION-20261025.md`, SHA256
`5E969DFBFB3E08B2C2CA5A7859683F914FEB3236486B51691FD4D77BE774C78D`
(hash placeholder to be replaced after final read; see §7).
Decision owner: transport. Status in document: BINDING CONVENTION B_I-zero.

## 0. Verdict

The central decision **B_I-zero** is correct and binding for the cited IV
Thm1.10 computation. The shell-positive formulas are also supported by the
cited AbsTopIII statements. However:

1. `log10 D_3` and `log10 D_273` in the decision are numerically wrong; the
   quoted values 40.6999 and 3878.7598 are `log10` of the **radius**, not of the
   natural deficit `D` (correct `log10 D` are about 1.9718 and 3.9509).
2. The number `((l+5)/4) log pi` is not the IV **maximal container** bound; it
   is the **procession-normalized weighted-average** upper bound obtained at
   the end of Thm1.10 proof Step (vii). The pointwise container bound is
   `(j+1) log pi`.
3. `D_C^Sp = d_p log p`, the b=3/b=273 deficits, and hence the radii
   `p^{d_p}` are **conditional** on the corrected finite-donor/target-container
   input; they are not paper-level IV statements.
4. The general weight formula `alpha_v = d_v/[F:Q]` is a normalization
   inference; IUT IV Remark1.7.1 gives product-normalized weights, and the
   simple `alpha_v` formula is exactly the `F_mod=F` single-radial-place
   specialization. For `F=Q` (the decisive route) it is correct.

Nothing in this audit gives a new attack or changes a target. The B_I-zero
conclusion stands; the numeric labels and one source attribution need repair.

## 1. Paper evidence checked

Corpus:

- `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt`
  (cited below as IV).
- `papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt`
  (cited as AbsTopIII).
- `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`
  (cited as III).

### 1.1 B_I definition and invariance (IV Prop1.5(iii))

IV lines 847-888: for finite nonempty `I,V`, `M_I = ⊗_{i∈I} M_i` with the
tensor product metric; `B_I ⊆ M_I` is the integral structure given by the
direct product of the unit balls of the copies of `C` in the unique direct sum
decomposition of `M_I`; the tensor/direct-sum metrics and `B_I` are preserved
by primitive automorphisms (lines 879-888).

**Classification: BINDING.** The decision's description of `B_I` and its
preservation is faithful. The cited pages 15-16 are correct (page markers at
IV lines 829 and 885).

### 1.2 B_I-zero normalization (IV proof Thm1.10 Step(vii))

IV lines 1836-1853:

```text
π^{j+1} · B_I
serves as a container for the union of possible images ...;
an upper bound for the log-volume of this container ... (j+1)·log(π)
follows immediately from the fact that [in order to ensure compatibility with
arithmetic degrees ... one is obliged to adopt normalizations which imply that]
the log-volume of B_I is equal to 0.
```

The sentence is explicit: the normalization is chosen so that `logvol(B_I)=0`;
the container `π^{j+1}B_I` then has log-volume at most `(j+1)log π`, and the
proof uses this. This is a B_I-zero convention, not a shell-zero convention.

**Classification: BINDING.** The decision's main conclusion is correct.

Caveat: this is a normalization adopted inside the IV Thm1.10 argument for
compatibility with arithmetic degrees; it is binding for that computation, not
a claim that every other normalization is mathematically inconsistent.

### 1.3 B_I-zero versus AbsTopIII unit-ball normalization

AbsTopIII Definition 4.1 (lines 5289-5295) defines, for a complex archimedean
field `k`, `O_k ⊆ k` as the subset of elements of absolute value `≤ 1`;
`O_k^×` as elements of absolute value `=1`.

AbsTopIII Prop5.7(ii)(a) (lines 7961-8005) defines the radial volume `μ_k`
with normalization `μ_k(O_k)=1` and radial log-volume `μ_k^log=log μ_k`.
Thus the unit ball has radial log-volume `0`; by the scaling property
(Prop5.7(ii)(b), lines 8006-8022) for `x∈k^×`, `μ_k^log(xA)=μ_k^log(A)+log|x|`
(in the radial/real-positive case), so a radial ball `B(r)` has log-volume
`log r`.

**Classification: BINDING for the local unit-ball normalization and the
`log r` radial formula.** The decision's use is correct, with the convention
that `O_k` is the closed unit ball.

### 1.4 Shell log-volume is log π, not zero

AbsTopIII Prop5.8(vi) (lines 8166-8192), especially lines 8190-8192:

```text
μ^log(G)(I(G)) = ˘μ^log(G)(O^×_{k~(G)}) − log(2)·F(G)/(2π)
               = log(π)·F(G)/(2π).
```

With the normalized representative `F(G)=2π`, this is `log π`. Hence the
archimedean log-shell is **not** the zero reference; its normalized log-volume
is positive. This rules out the shell-zero convention as a reading of the
paper's normalization.

**Classification: BINDING.** The decision's shell-positive statement is
correct.

### 1.5 IUT III archimedean shell radius

IUT III Remark1.2.2(ii) (lines 2223-2241) states that for `v∈V_arc`, with
`k=K_v`, the log-shell corresponds to

```text
I_k = {a∈k | |a| ≤ π} ⊆ k.
```

This supports the radius `π` used in the decision. The condition
`r_v≤π` is the source shell-containment condition, not a proved property of an
arbitrary complete source `C`.

**Classification: BINDING definition; CONDITIONAL as a premise.** The shell
radius is paper-level; the claim that the actual archimedean hull lies in the
shell is not proved by the decision and is correctly marked as a branch
condition.

## 2. Formula audit

### 2.1 `h_inf = Σ alpha_v log r_v`

IV Remark1.7.1 (lines 1009-1049) says that IV §1 uses normalized log-volumes
of Prop1.4(i), and that the III Remark3.1.1(ii) weights
`[K_v:Q_vQ]·[K_v:(F_mod)_v]^{-1}` must be replaced by
`[(F_mod)_v:Q_vQ]`; for `F_mod=F`, this is `d_v`, and after normalizing the
weights by their total, `alpha_v=d_v/[F:Q]`.

Thus for the **single radial readout** `F_mod=F`,

```text
h_inf = Σ_{v|∞} alpha_v log r_v = (1/[F:Q]) Σ d_v log r_v,
Σ_{v|∞} alpha_v = 1,  d_v=1 (real), 2 (complex).
```

**Classification: BINDING for `F_mod=F` and the radial single-place reading;
CONDITIONAL as a general formula for arbitrary IV product weights.** The
decision's `F=Q` special case `d_v=1`, `alpha=1`, `h_inf=log r_inf` is
binding.

Warning correctly stated by the decision: using `d_v log r` locally together
with `alpha_v=d_v/[F:Q]` would double-count `d_v`. The equivalent form
`(1/[F:Q]) Σ d_v log r_v` is consistent.

### 2.2 Shell containment: `h_inf ≤ log π`, not `≤0`

Under the B_I-zero/unit-ball normalization, `h_inf=Σ alpha_v log r_v`; if
`r_v≤π` for all archimedean `v`, then

```text
h_inf ≤ Σ alpha_v log π = log π = 1.1447298858494...
```

because `Σ alpha_v=1`. This is the correct replacement for `h_inf≤0`. The
shell's log-volume is `log π` as in §1.4, so the old shell-zero normalization
is not the paper's global normalization.

**Classification: CONDITIONAL (on shell containment) but formula correct.**
The decision's `h_inf≤log π` is based on the correct paper normalization.

### 2.3 Compensation radius

Given `h_inf=log r_inf` and `D_C^Sp=d_p log p`, the condition
`h_inf≥D_C^Sp` is equivalent to

```text
log r_inf ≥ d_p log p  ⇔  r_inf ≥ exp(d_p log p)=p^{d_p}.
```

No factor `π` appears. If instead the shell reference were zero, one would
have `h_inf=log(r/π)` and `r≥π p^{d_p}`; that is an alternative normalization
and is not the B_I-zero paper normalization.

**Classification: ALGEBRAICALLY CORRECT conditional formula.** The radius
formula is correct given the definition `D_C^Sp=d_p log p`; the numerical
`d_p` and hence the radius are conditional on the finite-donor derivation
(see §4).

### 2.4 `A_arc = ((l+5)/4) log π`

IV lines 1853-1859: after the weighted average and procession normalization,
the bound is

```text
(l+5)/4 · log(π) ≤ (l+1)/4 · 4    (for l≥5).
```

For `l=41`, `(l+5)/4=46/4=11.5`, so `A_arc=11.5 log π=13.164393687...`.
The fixed-`j` container bound is `(j+1) log π`; the `(l+5)/4` expression is
the final procession-normalized weighted average, not a universal pointwise
`max` over all `j`.

**Classification: DERIVED/conditionally correct inequality, but the label
'IV maximal-container bound' is a source-attribution error.** If the decision
uses `A_arc` only as a sufficient final bound after procession normalization,
the inequality is valid. It is not the raw container bound, and one should not
infer `h_inf≤A_arc` for an arbitrary fixed high capsule from it. For the
reported profiles the distinction is harmless for the qualitative exclusion
since the finite deficits are far larger, but the statement must be repaired.

### 2.5 Numeric checks

Computed independently with natural logarithms, `p=12301` (values rounded):

| quantity | decision value | independent check | verdict |
|---|---:|---:|---|
| `D_3=(408/41)log 12301` | 93.7149712746 | 93.71497127459669 | correct |
| `log10(r_3)` | 40.6998948963 | 40.699894896279 | correct (this is log10 radius) |
| `log10 D_3` (as printed) | 40.6998948963 | 1.9718089764 | **wrong label/value** |
| `r_3=12301^{408/41}` | 5.0106595585e40 | `10^{40.6998948963}` | correct |
| `D_273=(38883/41)log 12301` | 8931.17457860 | 8931.174578603292 | correct |
| `log10(r_273)` | 3878.759836402 | 3878.7598364020096 | correct (radius) |
| `log10 D_273` (as printed) | 3878.759836402 | 3.95090857865 | **wrong label/value** |
| `r_273=12301^{38883/41}` | log10 3878.759836402 | same | correct radius |
| `B=I` branch `38463/41` | log10 radius 3836.862885 | 3836.86288577349 | correct radius; conditional branch |
| `A_arc=11.5 log π` | 13.164394... | 13.1643936873 | correct |
| shell-pi withdrawn `π·12301^{408/41}` | log10 41.1970 | 41.1970447690 | correct for alternative convention |

The two printed lines `log10 D_3=40.699...` and `log10 D_273=3878.759...`
are inconsistent with the preceding `D` values: `log10(93.7149)≈1.9718`,
`log10(8931.17)≈3.9509`. The quoted numbers are `log10 r`, not `log10 D`.
This is a **notation/numeric error**, not an error in the radius formula or in
the B_I-zero conclusion. It should be corrected in the decision and in any
downstream text that repeats it.

## 3. Binding / conditional / error classification

| item | classification | reason |
|---|---|---|
| `logvol(B_I)=0` | **BINDING** | IV proof Thm1.10(vii), lines 1850-1853 |
| container `π^{j+1}B_I`, bound `(j+1)logπ` | **BINDING** | IV lines 1836-1849 |
| `B_I` = direct product of unit balls | **BINDING** | IV Prop1.5(iii), lines 879-888 |
| AbsTopIII unit ball `μ_k(O_k)=1`, `O_k={|a|≤1}` | **BINDING** | AbsTopIII Def4.1, Prop5.7(ii)(a) |
| radial `μ^log(B(r))=log r` | **BINDING consequence** | Prop5.7(ii)(a)+(b) scaling |
| `μ^log(I(G))=log π` | **BINDING** | AbsTopIII Prop5.8(vi), lines 8190-8192 |
| shell radius `π` | **BINDING definition** | IUT III Rmk1.2.2(ii), lines 2233-2234 |
| `h_inf=Σ alpha_v log r_v` for `F_mod=F` | **BINDING/derived** | IV Rmk1.7.1 weights plus scaling |
| `alpha_v=d_v/[F:Q]` for arbitrary IV product weights | **CONDITIONAL** | Rmk1.7.1 weights are product-normalized; formula is the single-radial `F_mod=F` specialization |
| `h_inf≤log π` under `r_v≤π` | **CONDITIONAL** | depends on actual shell containment; formula correct |
| `h_inf=log r_inf` for `F=Q` | **BINDING/derived** | `d_v=1`, `alpha=1` under above |
| `D_C^Sp=d_p log p` and b=3/b=273 values | **CONDITIONAL** | finite deficit depends on corrected symplectic donor/orbit/source naturality; not paper fact |
| `r_inf≥p^{d_p}` | **CONDITIONAL on D** | algebraically correct if `D=d_p log p` |
| `A_arc=((l+5)/4)logπ` | **DERIVED**; `max container` label is an **error** | IV lines 1856-1857 give a procession-normalized bound, not raw max |
| `log10 D_3`, `log10 D_273` printed values | **ERROR** | values are `log10 r`; actual `log10 D` ≈1.9718,3.9509 |
| b=273 A/B branch labels | **CONDITIONAL** | A=38883/41, B=38463/41 per correction; branch not decided |
| `h_inf≤0` withdrawn | **BINDING correction** | shell log-volume is `logπ`, not 0 |
| shell-pi normalization | **ALTERNATIVE convention, not binding** | consistent only if one normalizes shell to 0; paper uses B_I-zero |
| Lean sign flip warning | **BINDING/independent** | Lean readout is negative log; paper radial readout is positive log |

## 4. Conditional finite-donor inputs

The decision's radii depend on `D_C^Sp=d_p log p` and on the numerical
`d_3=408/41`, `d_273=38883/41` (and B=I `38463/41`). Those numbers come from
the finite all-bad profile estimate, which the C9 correction files classify as
conditional on:

- the corrected symplectic donor `H=Phi^{-1}(Sp_{2g}(Z_p))`, not the withdrawn
  boundary-word/`rho(Mod)=Sp` construction;
- the 2025 trace basis / 2026 symplectic basis alignment (inferred);
- the trace target `Tr_{K/K^{(d=1)}}` and the tame totally ramified case;
- the low-ramification input `J=m`;
- the standard-lattice lemma, orbit generation (7), and volume gain (8);
- local naturality and target-container conditions TC-A..TC-H/TC-S.

Thus the statement `r_inf≥p^{d_p}` is a **conditional necessary condition**, not
an actual paper consequence and not an actual constructed radius. The decision
does note at the end that the full source `C`, CFTH/TC, and target conditions
remain open; the audit makes the donor dependence explicit.

## 5. Does any shell-π statement survive in another normalization?

Yes, as an **alternative convention**, but not as a paper-binding statement.
Under the alternative normalization

```text
logvol(I_v)=0,  I_v={|a|≤π},
```

one gets `h_inf=Σ alpha_v log(r_v/π)`, shell containment gives `h_inf≤0`, and
compensation gives `r_inf≥π p^{d_p}`. These formulas are internally consistent
for that convention. They are **not** binding for the IUT IV B_I-zero
normalization: IV explicitly sets `logvol(B_I)=0`, and AbsTopIII explicitly
computes `μ^log(I(G))=logπ`, not 0. Therefore:

- the shell-pi radii `π p^{d_p}` survive only as **alternative-normalization
  quantities**;
- in the binding B_I-zero convention the radius is `p^{d_p}` and the shell
  bound is `h_inf≤logπ`;
- one must never mix the two conventions in a single inequality.

This is exactly the decision's main conclusion, and it is correct.

## 6. Summary of corrections needed in the decision

1. Replace `log10 D_3=40.699...` by `log10 D_3≈1.9718089764`; keep
   `log10 r_3=40.6998948963`. Similarly `log10 D_273≈3.9509085787`, while
   `log10 r_273=3878.759836402`.
2. Rename `A_arc=((l+5)/4)logπ` as the **procession-normalized weighted-average
   upper bound**; the raw container bound is `(j+1)logπ`.
3. Mark `D_C^Sp`, `d_3`, `d_273`, `38463/41`, and all derived radii as
   **conditional on the corrected finite donor/TC inputs**, not paper facts.
4. Keep the B_I-zero, `h_inf=log r`, shell `≤logπ`, no-π radius, and
   shell-pi-not-binding conclusions, which are supported by the cited sources.

## 7. Status and citations

Paper evidence:

- IV Prop1.5(iii), corpus lines 847-888 (pp.15-16): `B_I` unit-ball integral
  structure and primitive invariance.
- IV proof Thm1.10 Step(vii), corpus lines 1836-1859 (pp.29-30):
  `π^{j+1}B_I`, `logvol(B_I)=0`, `(j+1)logπ`, procession bound
  `((l+5)/4)logπ`.
- IV Remark1.7.1, corpus lines 1009-1049 (pp.17-18): normalized weights.
- AbsTopIII Definition4.1, corpus lines 5289-5295: `O_k={|a|≤1}`.
- AbsTopIII Prop5.7(ii)(a)-(b), corpus lines 7961-8022 (pp.137-138):
  `μ_k(O_k)=1`, radial log-volume and scaling.
- AbsTopIII Prop5.8(vi), corpus lines 8166-8192 (p.141):
  `μ^log(I(G))=logπ·F(G)/(2π)`.
- IUT III Remark1.2.2(ii), corpus lines 2223-2241: archimedean shell
  `I_k={|a|≤π}`.

Input document audited:

- `tmp/sheaf/n8/closure/C9-NORMALIZATION-DECISION-20261025.md`.
  The file is read-only in this audit; its decision is accepted with the
  corrections above. No Lean/Project/target edit was made.

Verdict: **B_I-zero binding; h_inf/shell/radius formulas conditionally correct;
two numeric labels and one source-attribution label are errors; shell-pi only
survives as an explicitly alternative normalization. target_accepted=false.**

End of C9-AUDIT-NORMALIZATION-DECISION-20261025.