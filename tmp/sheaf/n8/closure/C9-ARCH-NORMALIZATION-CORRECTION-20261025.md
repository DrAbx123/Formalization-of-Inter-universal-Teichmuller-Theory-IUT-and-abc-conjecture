# C9 archimedean normalization/label correction

Task: task-171 (Correct archimedean normalization/label errors).
Owner: volumedet. Date: 2026-10-25. Stage1 correction only; no new attack;
no Lean/Project/target edits. Only this file written. `target_accepted=false`.

Inputs read: C9-AUDIT-LOG-ARCH-20261025.md (task-161), C9-AUDIT-ARCH-GLOBAL-
20261025.md (task-163), C9-ARCHIMEDEAN-20261025.md (task-150),
C9-ARCH-GLOBAL-20261025.md (task-156), C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md
(task-162), C9-RADIUS-CORRECTION-20261025.md (task-167), and the errata in
C9-IND1-GLOBAL-20261025.md / C9-SYMPLECTIC-SOURCE-20261025.md.

This file supersedes the normalization and radius statements corrected below.
It leaves the finite-donor and target-container gaps untouched.

## 0. Corrected items at a glance

1. A2/A3 are inconsistent: `d_v log(r/pi)` and `sum alpha_v log(r/pi)` cannot
   both be used with `alpha_v=d_v/[F:Q]`.
2. The audited IV normalization is `log-volume(B_I)=0`; the local radial
   readout is `log r` (normalized convention), not `log(r/pi)`.
3. Shell containment gives `h_inf <= log pi`, not `h_inf <= 0`.
4. Compensation `h_inf >= D` under B_I-zero gives `r_inf >= exp(D)`, i.e.
   `r_inf >= p^{d_p}`; the factor `pi` is absent.
5. The exponential base is the bad rational prime `p=12301`, not `e=41`.
6. For b=273, `38883/41` is the A=O_K branch deficit (h_A=-39156/41);
   `38463/41` is the B=I branch deficit (h_B=-38736/41). They must not be
   mixed.
7. task-150 §4 quotes the (15)-aligned `h_A=-411/41`, not formula (10), which
   includes the `-c j` term and gives about -15.122 for b=3.

## 1. Normalization convention

### 1.1 Local normalized readout (chosen convention)

The audited IV statement is

    log-volume(B_I) = 0,
    log-volume(pi^{j+1} B_I) = (j+1) log pi.        (IV-vii)

For a radial ball B_v(r) in F_v (d_v=1 for R, d_v=2 for C), the normalized
radial readout used in the global degree normalization is

    h_v^rad(B_v(r)) = log r.                          (N1)

with global degree weight

    alpha_v = d_v/[F:Q],   sum_{v|infty} alpha_v = 1.  (N2)

Thus

    h_inf(C) = sum_{v|infty} alpha_v log r_v
             = (1/[F:Q]) sum_v d_v log r_v.            (N3)

Equivalently, if one uses the geometric local readout `d_v log r_v`, the
global weight is `1/[F:Q]`, not `alpha_v=d_v/[F:Q]`.  Using geometric local
readout together with alpha_v double-counts d_v.  This is the exact A2/A3
inconsistency.

For F=Q, d_v=1, alpha_inf=1, and

    h_inf(C) = log r_inf.                              (N4)

### 1.2 What is withdrawn

- A2 `h_v^rad(B_v(r)) = d_v log(r/pi)` as a local factor to be multiplied by
  `alpha_v=d_v/[F:Q]`: withdrawn (d_v double count and wrong reference).
- A3 `h_inf=sum alpha_v log(r_v/pi)`: withdrawn under B_I-zero; the reference
  is 1, not pi.
- A5 `h_inf=log(r_inf/pi)` for F=Q: withdrawn; corrected is `log r_inf`.
- Any formula that mixes `d_v log(r/pi)` locally with `alpha_v` globally.

Under the older shell-reference convention (`I_v={|a|<=pi}` normalized to 0)
`log(r/pi)` and a radius `pi*p^{d_p}` would be consistent; but that is a
different normalization, not the audited IV B_I-zero one.  This correction
uses B_I-zero throughout.

## 2. Shell containment and sign

### 2.1 Shell bound

If the actual archimedean hull is contained in the source log-shell,
`r_v <= pi` for all v|infty, then by (N3)

    h_inf(C) <= sum_v alpha_v log pi = log pi.          (S1)

Using log pi = 1.1447298858... natural units.  The old `h_inf <= 0` is
withdrawn: under B_I-zero the shell has positive normalized log-volume
`log pi`, and containment only upper-bounds h_inf by `log pi`.

Qualitative survivor: if the finite deficit satisfies `D_C^Sp > log pi`, the
shell branch still cannot compensate, because `h_inf <= log pi < D_C^Sp`.
For the uniform bad profile this is true:

    b=3:   D=(408/41)log p = 93.7149712746... > log pi;
    b=273: D=(38883/41)log p = 8931.17457860... > log pi.

So the archimedean-only insufficiency conclusion survives for these profiles,
but the earlier sharper statement `h_inf<=0` does not.

### 2.2 Product-formula bound

With the B_I-zero normalization and product formula

    sum_v alpha_v log|x|_v + sum_p alpha_p v_p(x) log p = 0,   (P1)

and log r_v >= log|x|_v on the radial hull, we get

    h_inf(C) >= -sum_p alpha_p v_p(x) log p.                    (P2)

There is no `-log pi` term.  For finite-integral x (all v_p(x)>=0), P2 gives
`h_inf >=` a nonpositive number; it still does not force positive
compensation, but it also does not give the old `h_inf>=-log pi` formula.

### 2.3 Sign convention

The paper's radial B_I-normalized log-volume is positive: `log r` for r>1 and
`log pi` for the shell.  The Lean readout is negative:

    absLogAddHom K u = -Real.log ||u||,
    archimedeanDelta r = -Real.log r.

Any comparison of the paper formula with the Lean value must flip sign (or
use `-archimedeanDelta`).  This sign warning in task-150 remains VALID and
unchanged.

## 3. Compensation radius and base p

### 3.1 Correct conditional criterion

Let `D_C^Sp = d_p log p` for one bad p in F=Q.  Under N4, compensation
`h_inf >= D_C^Sp` is

    log r_inf >= d_p log p,
    r_inf >= exp(d_p log p) = p^{d_p}.                 (R-new)

The factor `pi` is absent.  In the older shell-reference normalization it
would be `r_inf >= pi*p^{d_p}`; that is a different convention and is not
used here.

### 3.2 b=3

    d_3 = 408/41,
    D_3 = (408/41) log 12301 = 93.7149712746... natural,
    log10 D_3 = (408/41) log10 12301 = 40.6998948963...,
    r_inf >= 12301^{408/41} = 5.0106595585... * 10^40.   (R3)

Common log of the radius is 40.6998948963..., not 41.1970.

### 3.3 b=273

    d_273 = 38883/41,
    D_273 = (38883/41) log 12301 = 8931.17457860... natural,
    log10 D_273 = (38883/41) log10 12301 = 3878.759836402...,
    r_inf >= 12301^{38883/41}.                            (R273)

Its common log is 3878.759836402..., not 3879.2570.

### 3.4 Withdrawn radii

- task-156 A18/A19 `pi*exp(D)` (no log p): withdrawn.
- task-162 D1/D2 `pi*41^{d_p}` (wrong base): withdrawn.
- task-167 R1/R7 `pi*p^{d_p}` (correct base but still shell-reference pi):
  under B_I-zero the `pi` factor is also withdrawn; corrected is `p^{d_p}`.
The lead's earlier note `b=3 ~1.57e41` corresponded to `pi*p^{d_p}`; under
B_I-zero it becomes `~5.01e40`.  The b=273 log10 `~3878.76` is the correct
B_I-zero value.

## 4. b=273 branch labels

From C9-UNIFORM-HULL and task-161 audit:

| branch | h value | Q_p (log p) | deficit Q_p-h | status |
|---|---:|---:|---:|---|
| A=O_K | -39156/41 | -273/41 | 38883/41 | conditional A branch |
| B=I | -38736/41 | -273/41 | 38463/41 | conditional, unproved |

The number `38883/41` is the **A=O_K** deficit, not B=I.  The B=I deficit is
`38463/41`.  task-156 used `-38736/41` (B=I) under a generic label while
calling the value B=O_K; task-150 §4 did the same.  Under the natural trace
alignment B=I is not actual, so the correct B=O_K row is `h_A=-39156/41`, and
the b=273 radius (if used) is `12301^{38883/41}`, not `12301^{38463/41}`.

## 5. task-150 formula (10) versus (15)

TAME (10) at rho=1 contains

    ell_j^Sp(10) = -(20/41) j - s_j - 41^{-(j+1)}.

Its uniform average is

    h_10 = -210/41 - 10 - (1/20) sum_{j=1}^{20} 41^{-(j+1)}
         ~= -15.122,

not `-411/41`.  The number `-411/41` is the (15)-aligned
`h_A=-(1/20)sum(s_j+1/41)`, with no `-c j` tensor-order loss.  task-150 §4
must label its table `(15)-aligned h_A`, or alternatively display `(10)` and
use `h_10`; the two cannot be mixed.

Survivor: the arch-only insufficiency conclusion used `h_A` and remains valid
for the aligned formula; only the label/source of the number changes.

## 6. What survives, conditionally

### 6.1 Survivors

- IV archimedean container bound `(j+1)log pi` and procession average
  `(l+5)/4 log pi`: valid under the cited IV normalization.
- Dimension factor of the tensor/direct-sum packet contributes zero
  normalized log-volume; only the radial factor matters.
- Lean-vs-paper sign warning: valid.
- Shell containment now gives `h_inf <= log pi`; for `D_C^Sp>log pi` this
  still rules out archimedean-only compensation in the shell branch.
- b=3 aligned value `-411/41`, Q_p=-3/41, deficit 408/41; b=273 A=O_K value
  `-39156/41`, Q_p=-273/41, deficit 38883/41; B=I values `9/41` and
  `-38736/41` remain conditional/not actual.
- Residual formula structure `Q_C-h_C <= D_C^Sp-h_inf(C)` survives; only
  `h_inf` normalization and radius conversion changed.

### 6.2 Conditional / not proved

- Actual complete-C archimedean hull and radius `r_v`; shell containment or
  positive radius.
- Finite `D_C^Sp` values: depend on corrected symplectic donor, inferred
  trace/symplectic basis alignment, orbit generation, local naturality.
- Target-container conditions TC-A..TC-H and TC-S; TAME (11)-(14) are not a
  target proof.
- Global weighted sum over all finite/infinite places and fixed q-volume
  class.
- `p_{vQ}=e` normalization quoted from III/IV; not independently re-read here.

## 7. Exact summary table

| quantity | corrected value |
|---|---|
| F=Q normalized h_inf | log r_inf |
| general h_inf | sum_v (d_v/[F:Q]) log r_v = (1/[F:Q]) sum_v d_v log r_v |
| shell r_v<=pi | h_inf <= log pi = 1.1447298858 |
| b=3 D | (408/41)log 12301 = 93.7149712746 |
| b=3 required r | 12301^{408/41} ~ 5.0106595585e40 (log10 40.6998948963) |
| b=273 A=O_K deficit | 38883/41 |
| b=273 B=I deficit | 38463/41 |
| b=273 required r (A branch) | 12301^{38883/41} (log10 3878.759836402) |
| task-150 §4 value | h_A=-411/41=(15)-aligned; not (10) |
| (10) b=3 h | ~-15.122 |
| Lean sign | absLogAddHom=archimedeanDelta=-log |

## 8. Status

This is a normalization/label correction only. It does not prove
`h_C>=Q_C`, does not select a finite B branch, and does not remove TC-A..TC-H
or TC-S. No new attack, no Lean/Project edits. Only this file written.
`target_accepted=false`; complete C9/P6 not proved.
