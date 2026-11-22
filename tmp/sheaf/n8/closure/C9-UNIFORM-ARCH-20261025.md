# C9 uniform arch lower h_inf >= -S3 or exact obstruction

Task: task-315 (retasked to uniform scope). Owner: volumedet. Date:
2026-10-25. Short theorem/exact obstruction only. No mixed profile, no
arbitrary r_v, no Lean/Project/target edits. Only this file written.
`target_accepted=false`.

## 0. Result

For the fixed uniform F_mod=Q, e=41, p=12301 profile (bad mass rho=1):

- B=I b=3 needs `h_inf>=-S_3=-12/41 logp=-2.7563226845...` natural units.
- B=O_K b=3 needs `h_inf>=D_3=408/41 logp=93.7149712746...`, which is
  **above** the IV container upper bound A=13.1643936873.
- B=O_K b=273 needs h_inf>=38883/41 logp=8931.1745786; B=I b=273 needs
  38463/41 logp=8834.7032846. Both exceed A.

Therefore:

1. No uniform arch lower bound is proved. The IV/B_I-zero normalization
   gives only the upper bound `h_inf<=A`.
2. The conditional uniform b=3 B=O_K profile cannot be rescued
   archimedeanly: its required lower bound is above A, so it remains a
   conditional counterexample (Q-h>=D_3-A=80.550577...>0 under the
   conditional finite/target inputs).
3. The b=273 rows are even farther above A and cannot be arch-rescued.
4. The b=3 B=I row has the lower requirement -S_3; it would be proved by a
   source containment `B_I subset H_C,inf` (h_inf>=0) or by a global
   unit/point in H_C,inf, but neither is supplied. B=I itself is also
   conditional/type-gapped, so this does not prove original uniform P6.

Mixed-profile thresholds are ignored: the mixed rho=1/2 profile is a
different profile (E3 profile change), not the fixed uniform target.

## 1. Uniform P6 arch requirements

In log-p units, with h_C=h_fin+h_inf and Q_C=Q_p:

| branch | h_fin/logp | Q_p/logp | P6 requires h_inf/logp >= |
|---|---:|---:|---:|
| b=3 B=O_K | -411/41 | -3/41 | D_3=408/41=9.9512195... |
| b=3 B=I | 9/41 | -3/41 | -S_3=-12/41=-0.2926829... |
| b=273 B=O_K | -39156/41 | -273/41 | 38883/41=948.3658536... |
| b=273 B=I | -38736/41 | -273/41 | 38463/41=938.1219512... |

In natural units (multiply by log p=9.4174358389):

    b=3 B=O_K:  93.71497127459669
    b=3 B=I:    -2.7563226845469613
    b=273 B=O_K: 8931.174578603292
    b=273 B=I:  8834.703284644149.

These are the only uniform requirements. The mixed-threshold numbers
(-0.0678, -5.676) do not apply.

## 2. IV container gives only an upper bound

Under the binding B_I-zero normalization the paper-level archimedean
container yields

    H_C,inf subset pi^{j+1}B_I,   h_inf <= A=11.5 log pi=13.164393687268102.

The inclusion direction is `H_C,inf` inside the container, not the reverse.
Thus:

- b=3 B=O_K: required 93.714971 > 13.164394. Impossible under the IV
  container. There is no arch lower bound of the required size.
- b=273 B=O_K/B=I: required ~8931/8835 > 13.164394. Impossible.
- b=3 B=I: required -2.756322; the IV upper bound is higher, so it does not
  contradict but also does not imply the lower bound.

## 3. Exact obstruction

Theorem 3.1. No source theorem in the current corpus implies
`h_inf>=-S_3` (nor any uniform arch lower bound sufficient for the B=O_K
b=3/b=273 rows) for the fixed uniform C. The IV/B_I-zero data only give an
upper bound; the actual archimedean possible-image hull H_C,inf is not
constructed.

Proof/obstruction. A source lower bound would need one of:

(A) `B_I subset H_C,inf`. Then h_inf>=0, hence h_inf>=-S_3. But the IV
    theorem gives `H_C,inf subset pi^{j+1}B_I`, not the reverse; the
    containment `B_I subset H_C,inf` is exactly a missing source input, not
    a consequence of B_I-zero normalization or Theta-gluing.
(B) a global unit u in F^times with u in H_C,inf. Product formula would
    give h_inf>=0, but there is no source map F^times -> H_C,inf.
(C) a global point x in H_C,inf with finite valuation sum at most S_3.
    No such point/membership is constructed.
(D) a direct computation of H_C,inf and its normalized volume. The actual
    H_C,inf/radial r_inf is missing (task-232), and E_j/Theta-gluing does
    not supply a map to it.

None of (A)-(D) is available. Product formula applies only to points
already known to lie in H_C,inf; Theta-gluing transports packets, not
archimedean points or B_I containment. Therefore `h_inf>=-S_3` is not
proved. For the B=O_K rows even `B_I subset H_C,inf` would be insufficient
(h_inf>=0 < D_3), and any stronger arch lower bound is capped by
A<D_3; so those rows are obstructed by the IV container itself.

## 4. Conditional theorem (B_I containment)

Theorem 4.1. If the actual archimedean hull contains the unit ball
`B_I subset H_C,inf`, then:

(i) h_inf>=0;
(ii) h_inf>=-S_3;
(iii) for the uniform b=3 B=I branch, P6 holds (h_C>=h_B+h_inf>=Q_p).

Proof. B_I has radius 1, so r_inf>=1 and h_inf=log r_inf>=0. The B=I
local value h_B=9/41 logp exceeds Q_p=-3/41 logp by S_3; adding h_inf>=0
preserves h_C>=Q_p. QED.

Caveat: `B_I subset H_C,inf` is not a source theorem. It is a conditional
hypothesis. Moreover it does not rescue the B=O_K b=3 row: for that row one
needs h_inf>=D_3=93.7, while B_I containment gives only h_inf>=0 and the
IV container caps h_inf<=A=13.16. The B=O_K row remains a conditional
counterexample.

## 5. Consequences for uniform P6

- Uniform b=3 B=O_K: arch rescue impossible under IV; conditional
  counterexample margin 80.55. The only way to avoid it is to fail another
  input (B branch/target/TC/finite donor), not an arch lower bound.
- Uniform b=3 B=I: needed arch lower -S_3; not proved; if B_I containment
  were proved, P6 would hold in that branch (conditional theorem 4.1).
- Uniform b=273: arch rescue impossible under IV (A<<required); conditional
  counterexample in either branch.
- No mixed profile is used.

## 6. Classification

PROVED (exact):

- Uniform arch requirements table.
- B=O_K b=3/b=273 requirements exceed A; arch rescue impossible.
- B=I b=3 requirement -S_3; IV gives no lower bound.
- Conditional theorem 4.1: B_I subset H_C,inf => h_inf>=0 and B=I b=3 P6.

CONDITIONAL:

- B_I subset H_C,inf, global unit/point in hull, actual H_C,inf;
- B=O_K/B=I branch actuality; finite/target/TC inputs.

IMPOSSIBLE/WITHDRAWN:

- proving the uniform B=O_K b=3/b=273 arch bounds within the IV container;
- deriving h_inf>=-S_3 from B_I-zero/container/Theta-gluing alone;
- any mixed-profile use for P6.

OPEN/MISSING:

- actual H_C,inf/r_inf; B_I containment; global point/unit membership;
- B branch/TC; original uniform P6.

## 7. Conclusion

For the fixed uniform profile, the needed arch lower bounds are 93.714971
(b=3 B=O_K), -2.756322 (b=3 B=I), 8931.174579 (b=273 B=O_K), and 8834.703285
(b=273 B=I) natural. The B=O_K rows exceed the IV upper A=13.164394 and are
arch-obstructed; the b=3 B=I row has no source lower bound. `B_I subset
H_C,inf` would prove h_inf>=0 and the b=3 B=I branch conditionally, but it is
not a source theorem and does not rescue B=O_K b=3. No mixed profile is used.

## 8. Status

Short uniform theorem/exact obstruction only. No arbitrary r_v, no Lean/
Project edits. Only this file written. `target_accepted=false`; P6 open.
