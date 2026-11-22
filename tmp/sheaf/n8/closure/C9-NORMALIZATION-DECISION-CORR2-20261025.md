# C9 normalization decision correction 2

Task: task-190. Date: 2026-10-25. Owner/executor: transport.
Stage: label/terminology correction only. No Lean/Project/target edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-AUDIT-NORMALIZATION-DECISION-20261025.md (task-186 audit) | 348 | 79384B32506BA7F1849BB140DC1C2CDF298748F569898417C0E8FEC3B7E10A6C |
| C9-NORMALIZATION-DECISION-20261025.md (decision) | 267 | 5E969DFBFB3E08B2C2CA5A7859683F914FEB3236486B51691FD4D77BE774C78D |
| C9-AUDIT-ARCH-BOUND-20261025.md | 182 | 1442822A1F43FE653687BD45BD0527E99A4A6DEB14A810ABFEFA8736DDD7C50B |

This correction accepts the audit's classification. It does not change the
binding B_I-zero decision; it corrects two numeric labels, one
source-attribution label, and makes the conditional dependence explicit.

## 1. Binding B_I-zero remains

Unchanged and binding:

    log-volume(B_I)=0

(IUT IV Prop1.5(iii), pp.15-16; proof of Thm1.10 Step(vii), pp.29-30,
lines 1848-1859). Consequently, for F=Q radial:

    h_inf = log r_inf,
    shell r_inf<=pi  =>  h_inf <= log pi = 1.1447298858494...,
    compensation h_inf>=D_C^Sp  <=>  r_inf >= p^{d_p}  (no pi factor),
    general h_inf = sum_v alpha_v log r_v,
    alpha_v=d_v/[F:Q] for F_mod=F single radial readout.

The shell-pi forms h_inf=log(r/pi), h_inf<=0, r>=pi*p^{d_p} remain
ALTERNATIVE normalization quantities, not binding. They must not be mixed with
B_I-zero formulas.

## 2. Correction 1: log10 D versus log10 radius

The decision printed the radius common logarithms under the labels
"log10 D_3" and "log10 D_273". That is a notation error. The correct values
are:

### 2.1 b=3

    d_3=408/41,
    D_3=(408/41)log 12301=93.714971274596...
    log10 D_3=1.9718089764...                       (correct deficit log)

    r_3=12301^{408/41}=5.0106595585e40,
    log10 r_3=40.699894896279...                    (correct radius log)

The number 40.6998948963 is log10 r_3, not log10 D_3.

### 2.2 b=273 A=O_K

    d_273=38883/41,
    D_273=(38883/41)log 12301=8931.174578603...
    log10 D_273=3.95090857865...                    (correct deficit log)

    r_273=12301^{38883/41},
    log10 r_273=3878.7598364020...                  (correct radius log)

The number 3878.759836402 is log10 r_273, not log10 D_273.

### 2.3 b=273 B=I check

    d_B=38463/41,
    D_B=(38463/41)log 12301=8834.703284644...
    log10 D_B=3.9461919682...
    r_B=12301^{38463/41},
    log10 r_B=3836.862885773...

The B=I branch is not selected; this row is a conditional arithmetic check,
not an actual radius.

### 2.4 Summary table

| quantity | value | label |
|---|---:|---|
| D_3 | 93.7149712746 natural | deficit |
| log10 D_3 | 1.9718089764 | deficit log |
| r_3 | 5.0106595585e40 | radius |
| log10 r_3 | 40.6998948963 | radius log |
| D_273 A | 8931.174578603 natural | deficit |
| log10 D_273 A | 3.9509085787 | deficit log |
| r_273 A | 12301^{38883/41} | radius |
| log10 r_273 A | 3878.759836402 | radius log |
| D_273 B | 8834.703284644 natural | conditional B=I |
| r_273 B | 12301^{38463/41} | conditional B=I |
| log10 r_273 B | 3836.862885773 | conditional B=I |

Do not write "log10 D=40.699..." or "log10 D=3878.759..." in any downstream
file. The former is a radius log; the latter is a radius log.

## 3. Correction 2: A_arc terminology

The IV proof of Thm1.10 Step(vii), pp.29-30, gives two different objects:

1. Fixed-j raw container bound:

       pi^{j+1} B_I,
       log-volume(pi^{j+1}B_I)=(j+1) log pi.                (C1)

2. After weighted average over j=1,...,m=(l-1)/2 and procession
   normalization:

       A_proc := ((l+5)/4) log pi
               = 11.5 log pi = 13.1643936873...             (C2)

for l=41.

Correct terminology:

- C1 is the raw container bound at a fixed capsule level j.
- C2 is the IV final procession-normalized weighted-average upper bound.
- C2 is NOT a raw maximal-container bound and NOT a universal pointwise
  bound for an arbitrary fixed high capsule j.

The old label "A_arc = maximal container" is a source-attribution error. Use
either:

    A_container(j) := (j+1) log pi,
    A_proc := ((l+5)/4) log pi.

For the arch-only exclusion of the conditional b=3/b=273 profiles, both the
raw fixed-level bound and A_proc are far below the finite deficits, so the
qualitative exclusion is unaffected. But the statement h_inf<=A_proc for an
arbitrary fixed capsule is not justified; only the procession-normalized
average is bounded by A_proc.

## 4. Correction 3: conditional flags

The following are not paper-level facts and must carry the corrected finite
donor/orbit/TC hypotheses:

- D_C^Sp=sum alpha_p d_p log p;
- d_3=408/41, d_273=38883/41, d_B=38463/41;
- b=3/b=273 deficits and B=I values;
- radii r_inf>=p^{d_p} and their numeric values;
- B_H=O_K under natural alignment; full barGamma branch undetermined;
- B=I 9/41 not actual under natural alignment; B=I 38463/41 conditional.

Conditional dependence:

    corrected donor H=Phi^{-1}(Sp), mapping-class/Dehn-twist source,
    inferred 2025/2026 basis alignment, trace target Tr_{K/K^{d=1}},
    low-ramification J=m, standard-lattice lemma, orbit generation T7,
    volume gain T8, local naturality, CFTH/TC-A..TC-H/TC-S.

If any of these is not supplied, the D/d_p/B/radius statements are formal
conditional expressions, not actual global data. No complete C satisfying
them is constructed.

The B_I-zero normalization itself (h_inf=log r, shell bound log pi, no-pi
radius formula) is independent of these finite-donor conditions; only the
numerical D and hence the numerical radii are conditional.

## 5. Corrected binding formulas

1. B_I-zero:
       log-volume(B_I)=0.
2. F=Q radial:
       h_inf=log r_inf.
3. General:
       h_inf=sum_v alpha_v log r_v, alpha_v=d_v/[F:Q] for F_mod=F.
4. Shell:
       r_v<=pi => h_inf<=log pi, not 0.
5. Fixed-level container:
       log-volume(pi^{j+1}B_I)=(j+1)log pi.
6. Procession-normalized:
       A_proc=((l+5)/4)log pi=11.5log pi=13.1643936873...
7. Conditional compensation:
       h_inf>=D_C^Sp  <=>  r_inf>=p^{d_p}.
8. b=3 conditional:
       D_3=93.714971...; r_3=5.0106595585e40.
9. b=273 A conditional:
       D_273=8931.174579...; r_273=12301^{38883/41}.
10. Product formula:
       h_inf>=-sum alpha_p v_p(x)log p; no -log pi.

## 6. What this correction does not change

- The B_I-zero decision stands.
- h_inf=log r, shell h_inf<=log pi, radius p^{d_p} stand.
- Shell-pi remains an alternative normalization, not binding.
- E15 canonical/normalized d factor and B branch/CFTH conditions are untouched.
- No global closure, no complete C, no target acceptance.

## 7. Status

This file corrects the decision's numeric labels and container terminology
per the task-186 audit. It retains the binding B_I-zero convention and the
conditional finite-donor flags.

target_accepted=false.