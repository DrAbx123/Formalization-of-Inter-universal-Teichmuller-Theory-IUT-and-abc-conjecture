# C9 mixed-profile upper envelope and saturation U

Task: task-305. Date: 2026-10-25. Author: transport.
Short theorem/proof. No arbitrary profiles; no Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-TAME-LOG-DOMAIN-20261025.md | 250 | 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06 |
| C9-TARGET-GENERATED-20261025.md | 132 | F5139CDBB329133FF5A6E62E98CFBC9C5BF2E558B3491DE10A0CED97E04A4EBD |
| C9-UPPER-BOUND-20261025.md | 180 | 888413C9F3241BA6464D43C8C952EF50FBA1DEC0C1DE0FD86CEBF169A7EFE8EB |
| C9-P6-NOGO-20261025.md | 180 | 7B9BB3256363B6A8D0931E4E55C62D6FFA27E1FD2A0BF421DC35744D9167557D |

## 1. Result

The task-305 saturation upper bound is

    U:  h_C <= max(H_A,H_B) + h_inf,                           (1.1)

where H_A,H_B are the all-bad b-row finite values. The mixed-profile family
does NOT preserve U in the b=273 case:

- b=273: H_A=(-39156/41)log p, H_B=(-38736/41)log p,
  max=H_B=(-38736/41)log p<0. Mixed profiles have finite lower envelope
  approaching 0, so they exceed max(H_A,H_B). U is FALSE.

- b=3: H_A=(-411/41)log p, H_B=(9/41)log p, max=H_B>0. Mixed lower bounds
  are at most 0, hence do not violate U by themselves. U is not disproved by
  mixed lower bounds, but its actual upper-envelope validity is not proved.

Thus U survives (only as an unproved/non-violated condition) for b=3 B=I, but
fails for b=273. The mixed classes therefore cannot repair the b=273 upper
side; they make the hull larger and the surplus smaller.

## 2. TAME mixed lower bound

For a mixed bad/good profile with bad mass 0<rho<1, TAME Section 5 gives

    ell_j^aligned >= -rho^(j+1)(s_j+1/e),
    h_p^aligned/log p >= -(1/m) sum_j rho^(j+1)(s_j+1/e).      (2.1)

The all-bad A value is

    H_A/log p=-(1/m) sum_j (s_j+1/e).                          (2.2)

Since 0<rho<1 and s_j+1/e>0,

    -rho^(j+1)(s_j+1/e) > -(s_j+1/e),                          (2.3)
    -(1/m)sum_j rho^(j+1)(s_j+1/e) > H_A/log p.                (2.4)

For b=273, H_B>H_A (less negative). The mixed lower envelope is

    m(rho):=-(1/m)sum_j rho^(j+1)(s_j+1/e).                    (2.5)

As rho->0, m(rho)->0. Since H_B/logp=-38736/41<0, there is rho0 with
0<rho<rho0 => m(rho)>H_B/logp. Any such mixed region, if present in H_C,
exceeds the b=273 max row.

## 3. b=273 failure and extra volume

Quantify the extra over the max row:

    m(rho)-H_B/logp
      = -(1/m)sum_j rho^(j+1)(s_j+1/e) + 38736/41.             (3.1)

As rho->0 this tends to

    38736/41 = 944.7804878...                                   (3.2)

in log-p units. In natural units:

    (38736/41) log 12301 = 8897? compute: 38736/41*9.4174 = 8897.3 natural. (3.3)

The precise numerical value is not essential; the limit is the whole negative
of H_B. Thus mixed classes can raise the finite hull by an amount approaching
the full size of the b=273 B=I all-bad value. U with max(H_A,H_B) fails for
b=273 by up to 944.78 log-p units of finite volume.

For comparison, the b=273 B=I all-bad surplus is

    D_B=(38463/41)log p=938.121951... logp units,             (3.4)

so the mixed extra (up to 944.78) exceeds D_B by

    38736/41 - 38463/41 = 273/41 = 6.6585... logp units.      (3.5)

This means mixed profiles can eliminate the b=273 B=I positive surplus at the
level of the lower envelope. It does not prove P6, because an upper bound on
the actual mixed H_C is still missing.

## 4. Target inclusion

Assume TC-B: H_C is the hull of the full possible-image union. The TAME mixed
source region is an actual possible image under the allowed Gaussian/
permutation transport. Then

    h_C >= m(rho)+h_inf.                                      (4.1)

For b=273 and rho small, m(rho)>H_B/logp, hence

    h_C > H_B+h_inf = max(H_A,H_B)+h_inf.                     (4.2)

This is a direct counterexample to U for b=273. It is not an arbitrary choice:
the mixed regions are the source construction, and any sufficiently small
rho gives a violation.

If one refuses the mixed source inclusion, TC-B fails; then the target hull is
not the full possible-image hull, so the saturation U is not the target upper
bound either.

## 5. Does mixed failure rescue P6?

The sign is important:

    F=Q_C-h_C.

A larger h_C makes F smaller. Mixed classes raise h_C above the all-bad max, so
they **decrease** F. In the b=273 B=I all-bad profile F is positive (conditional
counterexample). Mixed extra up to 944.78 logp can reduce or eliminate that
positive surplus; hence mixed profiles can rescue P6 for those profiles, but
only if an upper bound on their actual h_C is available.

What is proved:

- U (upper bound by max) fails for b=273 mixed profiles.
- The mixed lower envelope exceeds the all-bad max and can exceed the b=273
  B=I surplus.
- Without an upper bound on the actual mixed h_C, no P6 conclusion follows.

What is not proved:

- an upper bound h_C<=mixed-envelope+h_inf;
- actual h_C for mixed profiles;
- actual h_inf and target inclusion;
- complete C/TC.

Thus mixed classes neither repair U nor prove P6; they show U is false and
that the b=273 counterexample needs mixed-profile control.

## 6. Exact obstruction

The saturation U fails for b=273 because:

1. mixed bad/good profiles exist (TAME Section 5);
2. their local finite lower envelope approaches 0 and exceeds the negative
   max(H_A,H_B)=H_B;
3. TC-B includes them in H_C;
4. the extra over max approaches 38736/41 logp = 944.78 logp, and can exceed
   the b=273 B=I all-bad surplus 38463/41 by 273/41 logp.

For b=3, max=H_B=9/41>0, and mixed lower bounds are below it; U is not
disproved by mixed lower bounds, but no upper-envelope proof exists.

## 7. Conclusion

The mixed-profile attack answers task-305:

    U survives for b=3 B=I only as a non-violated/unproved condition;
    U FAILS for b=273, with extra finite volume up to (38736/41)logp over H_B,
    exceeding the b=273 B=I all-bad surplus by (273/41)logp.

Therefore mixed classes do not repair the b=273 counterexample upper side;
they obstruct U and can, in principle, rescue P6 for mixed profiles only if an
actual upper bound on mixed h_C is supplied. No such upper bound is in the
frozen source.

No arbitrary profile was chosen; the TAME mixed regions and their lower bounds
are source data, and the violation holds for every sufficiently small rho.

target_accepted=false.
