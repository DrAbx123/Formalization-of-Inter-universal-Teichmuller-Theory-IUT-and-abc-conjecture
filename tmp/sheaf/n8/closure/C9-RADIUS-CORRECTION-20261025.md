# C9 radius correction: base p=12301, not 41

Task ID: task-167 / C9-RADIUS-CORRECTION-20261025. Owner: primespine. Date: 2026-10-25.
Nature: numerical/formula correction only; no new attack; no Lean/Project edits; only this file written.
Supersedes the numerical radii in C9-ARCH-GLOBAL-20261025.md (task-156) A18/A19 and C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md (task-162) D1/D2.

## 1. Correct formula

The finite residual is in log-p units:

    D_C^Sp = sum_{p in S_bad} alpha_p d_p log p,
    d_p = D_p^Sp/log p = b(e+1)/12 - (b-1)/e - T_p.

For F=Q and one real infinite place, the archimedean readout is

    h_inf = log(r_inf/pi).

Compensation h_inf >= D_C^Sp is therefore

    log(r_inf/pi) >= d_p log p,
    r_inf >= pi * p^{d_p}.                                  (R1)

Here p is the rational prime of the local bad place, not the ramification index e.
In the concrete C9 local type used by task-148/task-155/task-162:

    p = 12301,  e = 41,  K = Q_p(pi),  pi^41 = p.

Thus the base is 12301. The number 41 is e; it appears in d_p=408/41 or 38883/41 and in Q_p=-b/e log p, but it is not the base of the archimedean exponential.

Equivalently, using natural logarithms:

    r_inf >= pi * exp(d_p * log 12301).                     (R2)

The residual itself is

    Q_C - h_C <= d_p log 12301 - log(r_inf/pi),             (R3)

so the positive finite deficit at the reference radius r_inf=pi is d_p log 12301.

## 2. Exact recomputation for b=3

    d_3 = 408/41.

    D_C^Sp = (408/41) log 12301.                            (R4)

Natural-log value:

    (408/41) log 12301 = 93.71497127459669...               (R5)

Common-log value:

    (408/41) log10 12301 = 40.69989489627909...             (R6)

Therefore

    r_inf >= pi * 12301^{408/41}
          = 1.5741451258619... * 10^41.                     (R7)

Common log of the radius:

    log10 r_inf = log10 pi + (408/41) log10 12301
                = 41.1970447689732...                       (R8)

Old invalid values: task-156 A18 gave pi*exp(408/41) approx 65903.669 (this omitted log p entirely); task-162 D1 gave pi*41^{408/41} approx 3.51816e16 (this used base e=41 instead of p=12301). Both are withdrawn. The corrected required radius is about 1.57415e41, not 3.51816e16.

## 3. Exact recomputation for b=273

    d_273 = 38883/41.

    D_C^Sp = (38883/41) log 12301.                          (R9)

Natural-log value:

    (38883/41) log 12301 = 8931.17457860329...              (R10)

Common-log value:

    (38883/41) log10 12301 = 3878.75983640201...            (R11)

Therefore

    r_inf >= pi * 12301^{38883/41}
          = 1.8071170135918... * 10^3879.                   (R12)

Common log of the radius:

    log10 r_inf = log10 pi + (38883/41) log10 12301
                = 3879.25698627470...                       (R13)

Old invalid values: task-156 A19 used pi*exp(38883/41); task-162 D2 used pi*41^{38883/41} with log10 approximately 1530. Both are withdrawn. The corrected required radius has log10 approximately 3879.257, not 1530.

## 4. Corrected task-156 and task-162 references

Replace in C9-ARCH-GLOBAL-20261025.md:

- A18: pi*exp(408/41) approx 65903.669 -> pi*12301^{408/41} approx 1.57415e41.
- A19: pi*exp(38883/41) -> pi*12301^{38883/41} approx 1.80712e3879.

Replace in C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md:

- D1: pi*41^{408/41} approx 3.51816e16 -> pi*12301^{408/41} approx 1.57415e41.
- D2: pi*41^{38883/41} with log10 approximately 1530.0 -> pi*12301^{38883/41} with log10 approximately 3879.257.

The correction note added to task-162 said the earlier A18/A19 omitted log p. That diagnosis was correct, but the replacement base used there (41) was still wrong; this file corrects both the missing log p and the base, and therefore supersedes that note as well.

## 5. What remains unchanged

- The exact conditional residual formula (R3) is unchanged in structure: Q_C-h_C <= D_C^Sp-h_inf.
- d_3=408/41 and d_273=38883/41 are unchanged; only the exponential base changes from 41 to 12301.
- The b=3 B=O_K finite value -411/41 and the b=273 B=O_K value -39156/41 are unchanged; Q_p values -3/41 and -273/41 are unchanged.
- The conditional B=I values 9/41 and -38736/41 are unchanged but remain not actual under the natural trace alignment; this correction does not select B=I.
- The archimedean shell branch r_inf<=pi and the conditional compensation criterion h_inf>=D_C^Sp are unchanged.

## 6. Status

This is a numerical/formula correction only. It does not prove h_C>=Q_C, does not select a finite branch, and does not remove TC-A..TC-H/TC-S conditions. No new attack assumption was added.

Status: stage1 natural-language/exact computation only. Lean/Project/kernel/comparator/independent review not run. target_accepted=false; complete C9/P6 not proved.
