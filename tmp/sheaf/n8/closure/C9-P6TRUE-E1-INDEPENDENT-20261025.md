# C9 independent E1: b=273 complete-C impossibility

Task: task-347. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits; no mixed/E3; no arbitrary data.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- C9-B273-COMPLETE-C-20261025.md (task-258), 166 lines,
  SHA256 8cd5991aa2a8ad9528dd273f97c0baef6f1eaaf56fc1568ac049a2644a2ae437.
- C9-B273-COMPLETE-BPS-20261025.md (task-288), 91 lines,
  SHA256 739757d99c6aa23cf67925e3272ea0b146066ab8a95c4486b288d1b3c906bd8b.
- C9-B273-GLOBAL-BPS-20261025.md (task-292), 155 lines,
  SHA256 1284a14a6844692f13ad8503cba10eba0526c5d0cafdae577664b251e77b6ec7.
- C9-B273-BPS-EXCLUSION-20261025.md (task-284), 107 lines,
  SHA256 71c57b7879a6c1d38c5e4112aeda5ebbe53f731734e43d5be310d54c3c4bb699.
- C9-B273-CONSTRUCTION-20261025.md (task-257), 134 lines,
  SHA256 5353f7e8af722edf506f4c567a33ce3332d11fdcdbcbf26d69832491c148d500.
- C9-MOD41-UNCONDITIONAL-20261025.md (task-236), 204 lines,
  SHA256 4eaf8135eff70d6d5d79b6eb66a250f58b04a1e3ff4da6210624684a4d6f9c25.


## 1. Verdict

E1 (no admissible complete C with the b=273 profile) is **NOT proved**. The
b=273 profile is locally and degree-admissible; no frozen global BPS/Theta/
0-column/TC/CFTH constraint excludes it. A complete C with b=273 is also
**not constructed**: the missing objects are global, not b=273-specific.

Thus P6 is not established by E1. The b=273 P6 counterexample remains
conditional on an actual complete C plus the target inputs; it is not an actual
counterexample and E1 is not an actual exclusion.

## 2. What is actually admissible

The E_546 skeleton is source-valid:

    E_546: y^2=x^3+(3/M)x+(2/M), M=1728 p^546-1,
    j=1/p^546, v_p(Delta)=546, split I_546,
    q=p^546 u, qhat=pi^273 v, b=273, e=41, f=1.                 (2.1)

It satisfies:

- Def3.1(a): i in F, E[6] over F.
- Def3.1(b): M-prime III* degree4; 2 I0 good; 3 I0* degree2;
  [F:Q] 2,3-smooth, 41-free.
- Def3.1(c): q-order 273; 41 does not divide 273 or 546; local I_546;
  exact mod41 point counts give G=H=GL2(F41).
- Local BPS value data: q, qhat, theta ratios, Gaussian monoid, q-order273.
- q-order/BPS/Theta exponents at j<=20 are prime to41; weights rho^{j+1}=1;
  target normalization B_I-zero independent of b.

Therefore no local/defect arithmetic obstruction excludes b=273. The earlier
task-258 conclusion stands: b=273 is admissible at source-skeleton level.

## 3. What a complete C still needs

A complete C/BPS/Theta requires at least:

(i) explicit C_F/C_K/V/epsilon equations, stacky cusps, 41-division
    coordinates, K field equations, V/epsilon local coordinates;
(ii) the global BPS/F^{⊩▶×mu}-prime-strip: labels, etale/value portions,
     full poly-isomorphism gluing to the Theta-pilot 0-column;
(iii) the Theta-pilot possible-image set, theta/Kummer evaluation across all
      labels, target column, fixed q-volume class;
(iv) CFTH finite branch (H_A-full, B=O_K/B=I, kappa), actual archimedean
     H_C,inf, and TC-A..TC-H/TC-S.

E_546 and E_546[41] determine local q/theta data but do not determine (i)-(iv).
In particular, the BPS is an input F^{⊩▶×mu}-prime-strip to the multiradial
algorithm, not a function of the elliptic curve or its 41-torsion. Assigning a
BPS label/gluing or target column by hand would be arbitrary and is excluded.

## 4. E1 theorem and its proof stop

Theorem 4.1 (no local exclusion). Under the frozen source constraints, the
b=273 profile is not excluded by Def3.1(a)-(c), q-order, local type I_546,
2,3-smooth F, mod41 image, BPS/Theta level exponents, or B_I-zero target
normalization.

Proof. The listed checks are a direct re-listing of task-258/task-284/task-288:
41∤273 and 41∤546; local I_546; F 2,3-smooth 41-free; exact mod41 G=H=GL2;
all Theta/BPS level exponents j,T_j <=20 are prime to41; weights 1; target
B_I-zero. No one of these uses b=273 in a forbidden way. QED.

Corollary 4.2 (E1 not proved). E1 = "no admissible complete C with b=273" is
not a consequence of the frozen local/degree/order data. A proof of E1 would
need a genuine global obstruction in (i)-(iv), not a b=273 arithmetic defect.
No such obstruction is in the source.

Conversely, a complete C with b=273 is not constructed: (i)-(iv) are missing.
The exact first obstruction is the global BPS label/gluing datum, followed by
C_F/C_K/V/epsilon and CFTH/TC/arch.

## 5. Could global BPS/Theta/0-column force E1?

For E1 one would need one of:

(E1-a) a source identity in the global BPS/F^{⊩▶×mu}-prime-strip that is
       incompatible with q-order 273 / local I_546;
(E1-b) an integrality/gluing condition on the Theta-pilot 0-column or target
       column violated by b=273;
(E1-c) a TC/CFTH identity that cannot hold for any b=273 C;
(E1-d) a complete-C assembly contradiction independent of arbitrary label
       choices.

The frozen source gives:

- q-order/BPS/Theta constraints: satisfied, no inequality on b;
- 0-column: label/gluing data missing; no b-dependent obstruction;
- target column: B_I-zero normalization independent of b;
- TC/CFTH: conditional on actual y1/B/arch data, not b-specific.

No (E1-a)-(E1-d) is proved. Treating the absence of a constructed complete C as
E1 would be a logical error: non-construction is not impossibility. Assigning
BPS labels to create a contradiction would be arbitrary.

## 6. Consequence for P6

- E1: NOT PROVED.
- Complete C with b=273: NOT CONSTRUCTED.
- b=273 P6 counterexample: CONDITIONAL on an actual complete C + CFTH/TC/arch;
  not actual.
- P6: open; no P6-true proof and no actual counterexample from this angle.

The only honest E1 statement is:

    no b=273-specific local/arithmetic/order obstruction is known;
    every known missing object is global and shared with b=3.

## 7. Classification

| item | status |
|---|---|
| b=273 local/degree/mod41 admissibility | PROVED |
| q-order 41-coprimality, I_546 | PROVED |
| BPS/Theta level exponents prime to41 | PROVED |
| complete C with b=273 | NOT CONSTRUCTED |
| E1 no admissible complete C | NOT PROVED |
| E1-a..E1-d global obstruction | NONE in frozen source |
| b=273 P6 counterexample | CONDITIONAL on complete C |
| P6 true via E1 | NOT ESTABLISHED |

## 8. Conclusion

The independent E1 attack does not exclude b=273. The profile passes all local,
degree, q-order, mod41, and BPS/Theta order checks; the missing objects are the
global BPS/Theta-pilot/0-column/gluing/target-column, explicit C_F/C_K/V/epsilon,
and CFTH/TC/arch data. Non-construction of a complete C is not proof of
impossibility. E1 remains open, and P6 is not established. No arbitrary BPS
label or target column is assigned; no mixed/E3 profile is used.

No Lean/kernel closure; target_accepted=false; P6 open.

## 9. Status

- Short independent E1 theorem/proof/exact obstruction only; no Lean/Project
  edits.
- E1 not proved; complete C not constructed; b=273 conditional counterexample
  unchanged.
- target_accepted=false.
