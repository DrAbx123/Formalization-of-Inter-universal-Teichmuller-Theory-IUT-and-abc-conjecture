# C9 exact mixed-profile volumes for b=3 and b=273

> **SCOPE CORRECTION (task-307/Lead, 2026-10-25).** The mixed bad/good
> profile `0<rho<1` is a **different profile**, not a possible image of the
> fixed `F_mod=Q` uniform target. I Def3.1(e)'s V-section selects one place
> per rational prime, so the bad mass is `rho in {0,1}`; replacing unselected
> conjugates by `rho=1/2` is the E3 profile change explicitly forbidden by
> C9-GLOBAL §1. Therefore the mixed-profile computations and thresholds in
> this file are **profile-change/conditional** and are NOT usable for the
> original uniform P6. They do not prove a mixed P6 rescue, a mixed
> counterexample, or a mixed U refutation. The exact mixed arithmetic is
> retained only as a conditional different-profile result.

Task: task-304 (Exact mixed-profile volumes b=3/b=273). Owner: volumedet.
Date: 2026-10-25. Short theorem/exact computation only. No arbitrary rho, no
Lean/Project/target edits. Only this file written. `target_accepted=false`.

Inputs: C9-TAME-LOG-DOMAIN-20261025.md §5-§7 formula (15);
C9-UNIFORM-HULL-20261025.md; C9-ARCH-NORMALIZATION-CORRECTION-20261025.md.

## 0. Result

For the mixed bad/good profile of bad mass `rho in (0,1)`, the aligned
per-row and averaged finite lower bounds are

    ell_j^mixed(rho) = -rho^{j+1}(s_j+1/e),
    H_b(rho)/log p = -(1/m) sum_{j=1}^m rho^{j+1}(s_j+1/e),   (0.1)
    m=(e-1)/2=20, e=41, b j^2=s_j e+t_j, 1<=t_j<e.

with the profile-scaled native q local value

    Q_b(rho)/log p = -rho b/e.                                (0.2)

The function H_b(rho) is strictly decreasing on (0,1), with

    sup_{0<rho<1} H_b(rho) = 0 (not attained),
    inf_{0<rho<1} H_b(rho) = H_b(1)=H_A,                      (0.3)

where H_A is the all-bad A=O_K value. Hence there is a unique threshold
`rho*_b` with H_b>=Q_b exactly on `0<rho<=rho*_b`. The thresholds are
algebraic roots of an explicit polynomial:

    rho*_3   = 0.662770889969834162920306173...
    rho*_273 = 0.629869111334826128744553319... .              (0.4)

Thus mixed profiles with bad mass below the threshold satisfy P6
(`h>=Q`), while mixed profiles with positive-D (`Q-H>0`, i.e. above the
threshold) do NOT give a P6 lower bound: their lower bound is still below Q.
Above the threshold, increasing rho (toward all-bad) makes the deficit
worse, ending at H_A<Q. No mixed profile rescues a positive-D b=3 or b=273
profile.

## 1. Per-row and averaged formulas

TAME §5 (15) for the mixed profile gives

    ell_j^mixed >= -rho^{j+1}(s_j+1/e),
    H_b(rho) >= -(1/20) sum_{j=1}^{20} rho^{j+1}(s_j+1/e).    (1.1)

The same bad mass convention gives, as in TAME §7 (rho=1/2 table),

    Q_b(rho) = -(rho b/e) log p.                              (1.2)

In log-p units, define

    F_b(rho) := Q_b(rho)-H_b(rho)
             = -rho b/41 + (1/20)sum rho^{j+1}(s_j+1/41)
             = (rho/20) [ 20b/41 - sum (s_j+1/41) rho^j ].   (1.3)

P6 is `F_b(rho)<=0`; positive D means `F_b(rho)>0`.

## 2. Threshold polynomial

Define

    G_b(rho) := sum_{j=1}^{20} (s_j+1/41) rho^j - 20b/41.       (2.1)

Then `F_b(rho)=-(rho/20)G_b(rho)`, so for rho>0,

    F_b(rho)<=0  <=>  G_b(rho)>=0.                            (2.2)

`G_b` has positive coefficients and is strictly increasing on (0,1).
Also `G_b(0)=-20b/41<0`; at rho=1,

    G_b(1)=sum(s_j+1/41)-20b/41 >0

because the all-bad A value satisfies `H_A<Q_b(1)` for b=3 and b=273. Thus
there is a **unique** `rho*_b in (0,1)` with `G_b(rho*_b)=0`, and

    P6 holds  <=>  0<rho<=rho*_b;
    positive-D (Q>H)  <=>  rho*_b<rho<1.                      (2.3)

## 3. Exact data for b=3

    s_j(3)=[0,0,0,1,1,2,3,4,5,7,8,10,12,14,16,18,21,23,26,29],
    sum s_j=200.

    G_3(rho)=sum_{j=1}^{20}(s_j+1/41)rho^j - 60/41.

Unique root in (0.662770,0.662771); high-precision value

    rho*_3=0.662770889969834162920306173368612...
    H_3(rho*_3)=Q_3(rho*_3)=-0.0484954309734024997... (log-p units).

All-bad comparison:

    H_A(3)=H_3(1)=-411/41=-10.0243902439... (log-p units),
    H_B(3)=9/41=0.2195121951... (conditional B=I all-bad),
    Q_3(1)=-3/41=-0.0731707317... .

Thus `H_3` decreases from 0 to `H_A(3)`; it is always below `H_B(3)`; for
rho>rho*_3 it is below Q, so the mixed A-profile has positive D and cannot
prove P6. The TAME §7 rho=1/2 value -0.005370... > Q=-3/82=-0.036585... is
consistent: 1/2<rho*_3.

## 4. Exact data for b=273

    s_j(273)=[6,26,59,106,166,239,326,426,539,665,805,958,1125,1305,
              1498,1704,1924,2157,2403,2663],
    sum s_j=19100.

    G_273(rho)=sum_{j=1}^{20}(s_j+1/41)rho^j - 5460/41.

Unique root in (0.629869,0.629870); high-precision

    rho*_273=0.629869111334826128744553319223516...
    H_273(rho*_273)=Q_273(rho*_273)=-4.1940065218148178816... (log-p units).

All-bad comparison:

    H_A(273)=H_273(1)=-39156/41=-955.0243902439... (log-p units),
    H_B(273)=-38736/41=-944.7804878049... (conditional B=I all-bad),
    Q_273(1)=-273/41=-6.6585365854... .

Again `H_273` decreases from 0 to `H_A(273)`; for rho>rho*_273 it is below Q,
so positive-D mixed profiles have no P6 lower bound.

## 5. Sup/max and comparison

For both b:

    H_b'(rho)=-(1/20)log p sum_{j=1}^{20}(j+1)rho^j(s_j+1/e)<0,

so H_b is strictly decreasing; it has **no attained maximum or minimum** on
the open interval (0,1). The supremum is 0 at rho->0; the infimum is H_A at
rho->1 (all-bad). The all-bad A value H_A is the worst uniform lower bound
over mixed profiles; H_B (conditional B=I) is higher than H_A but is not
produced by the mixed A-profile formula.

Comparison summary (log-p units):

| b | rho* | H(1)=H_A | H_B (cond.) | Q(1) |
|---:|---:|---:|---:|---:|
| 3 | 0.6627708899... | -411/41=-10.02439 | 9/41=0.21951 | -3/41=-0.07317 |
| 273 | 0.6298691113... | -39156/41=-955.02439 | -38736/41=-944.78049 | -273/41=-6.65854 |

## 6. P6 theorem / exact obstruction

Theorem 6.1. For b=3 or b=273, under the mixed TAME profile bound (1.1) and
the profile-scaled native q value (1.2):

(i) P6 (`H_b(rho)>=Q_b(rho)`) holds exactly for `0<rho<=rho*_b`;
(ii) for `rho*_b<rho<1` the mixed lower bound is below Q, so the profile has
     positive D and no P6 lower bound follows;
(iii) no mixed profile in (0,1) attains a positive H or a maximum; the
      uniform worst case is H_A<Q(1);
(iv) mixed profiles cannot rescue a positive-D b=3 or b=273 profile: above
     the threshold, increasing bad mass only decreases H toward H_A.

Proof. `F_b=-(rho/20)G_b`, `G_b` strictly increasing, G_b(0)<0, G_b(1)>0;
unique root; signs. Monotonicity of H from its negative derivative. The
all-bad comparison is direct evaluation. QED.

Exact obstruction: there is no rho in (0,1) with `rho>rho*_b` and
`H_b(rho)>=Q_b(rho)`; in particular no mixed profile with positive D gives
the desired lower bound. The only profiles satisfying P6 are the small-bad-mass
ones below the threshold, which are not positive-D. A conditional B=I branch
could raise h above Q locally, but it is not part of the mixed A bound and is
not actual (B branch untraced).

## 7. Classification

PROVED (exact):

- per-row and averaged mixed formulas;
- strict monotonicity and sup/inf of H_b;
- unique threshold polynomial G_b and numerical roots rho*_3, rho*_273;
- P6 iff rho<=rho*_b; positive-D iff rho>rho*_b;
- all-bad H_A/H_B and Q values; mixed H lies between H_A and 0 and does not
  reach H_B;
- no mixed rescue of positive-D profiles.

CONDITIONAL:

- TAME §5 aligned profile formula and Q_b(rho)=-rho b/e;
- actual target/normalization; B=I alternative not included;
- the threshold applies to the mixed A-profile only, not all source outputs.

IMPOSSIBLE/WITHDRAWN:

- a mixed profile with positive D and H>=Q;
- treating sup H=0 as an attained positive compensation;
- comparing H to all-bad Q=-b/e instead of profile-scaled -rho b/e;
- using mixed A formula to reach conditional H_B.

OPEN: actual complete C/BPS/target/arch; B branch; global P6.

## 8. Conclusion

The exact mixed-profile volumes are strictly decreasing from sup 0 to
all-bad H_A. The thresholds are rho*_3=0.6627708899... and
rho*_273=0.6298691113..., with H=Q at the threshold. Mixed profiles with
rho below threshold satisfy P6, but they are not positive-D; mixed profiles
with positive-D (rho above threshold) have H<Q and do not give a P6 lower
bound. No mixed profile rescues the positive-D b=3/b=273 profiles, and no
attained maximum or positive mixed height exists.

## 9. Status

Short exact computation/theorem only. No arbitrary rho beyond the profile
parameter interval, no Lean/Project edits. Only this file written.
`target_accepted=false`; P6 open.
