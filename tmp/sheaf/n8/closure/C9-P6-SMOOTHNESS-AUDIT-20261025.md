# C9 P6 NATURAL-LANGUAGE SMOOTHNESS AUDIT

Date: 2026-10-25. Status: P6 OPEN. No Lean proof claimed.

## 0. Verdict

The natural-language P6 chain is NOT yet smooth enough for Lean.
It is a conditional schema with named obligations, not a linear proof.
Starting Lean now would only encode the same assumptions as fields/sorry-like
hypotheses; it would not establish P6.

## 1. What is smooth

- A1 q-pilot input/representation: source-input, expanded in
  C9-P6NORM-A1-20261025.md from Def3.8/Rem3.11.1/Steps xi-a-c.
- q-pilot numerical value under C9 normalization:
  q_v=p^{2b}u, qhat=q_v^{1/82}=pi^b v,
  -|log q|=-(1/82)v_p(q_v)logp=-(b/41)logp.
  This is exact once the C9 82-root normalization is fixed
  (C9-P6NORM-QVALUE-20261025.md).
- Cor3.12 statement itself: -|logTheta| >= -|log q|.

## 2. What is NOT smooth

B1. A2 determinant/log-volume comparison.
    Missing: explicit det^{tensor M}, O(-)^{-1}, integer M, normalization
    factors, degree=log-volume identity, tensor-twist invariance,
    upper-semi compatibility, hull approximant, vertical shift.
    Source says 'We leave the routine details to the reader'.

B2. A3 SHE fixed-value inclusion.
    Source says the inclusion holds 'perhaps only up to some sort of
    approximation'. Exact membership -|log q| in R_{<=-|logTheta|} is not
    set-theoretically derived. SHE -> membership is source-asserted.

B3. T_norm target translation.
    Need N1 B_I=O_v; N2 C9 finite reference/source O; N3 procession average;
    N4 global weights/C6. Without these, h_C and Q_C are C9 quantities,
    not source -|logTheta|/-|log q|.

B4. Canonical vs normalized target.
    Q_canon=d Q_norm, h_canon=d h_norm, d=41.
    P6_norm: Q_norm<=h_norm. P6_canon: Q_canon<=h_canon.
    Mixed target Q_canon<=h_norm is FALSE/off by 41.
    The target convention must be fixed before any Lean statement.

B5. A1 residual objects.
    q_v up to torsion; no canonical q; input is a poly-isomorphism class;
    output is a collection of possibilities, not a canonical section.

## 3. Smoothness criteria before Lean

1. Fix the target: P6_norm or P6_canon. No mixed convention.
2. Replace A2 by an exact chain of equalities/inequalities with all
   determinant/normalization factors displayed.
3. Replace A3 by either exact set-membership or an explicit error term
   epsilon with a proved sign/bound; no 'perhaps up to approximation'.
4. State and prove T_norm hypotheses N1-N4, or define C9 h_C/Q_C so that
   T_norm is definitional and record that choice.
5. Decide whether the Lean statement uses normalized or canonical quantities;
   do not encode factor 41 silently.

## 4. Consequence for Lean

A Lean statement layer can be written only after 1-5 are fixed. A conditional
Lean structure can encode the current 19 named obligations, but that is not a
proof of P6 and should not be reported as closure.

B6. Arch normalization and the P6_norm/P6_canon distinction (task-395).
    C6 1/D normalization applies to the finite bad block only; h_inf is not
    divided by d. Exact global relation:
      h_C = h_bad_can/d + h_inf,
      h_can = h_bad_can + h_inf = d*h_C - (d-1)*h_inf,
      Q_can = d*Q_norm.
    Cor3.12 gives Q_can <= h_can, hence
      Q_norm <= h_C - ((d-1)/d)*h_inf.
    Therefore:
      P6_can (Q_can<=h_can): exact Cor3.12 target.
      P6_norm (Q_norm<=h_C): follows from Cor3.12 only if h_inf>=0;
      without h_inf>=0 it is NOT implied. h_inf>=0 is unproved.
      Mixed target Q_can<=h_C is off by d and arch.
    This must be fixed before any Lean statement.

B7. Conflict between task-395 and task-397 on the arch factor.
    task-395: h_C = h_bad_can/d + h_inf; P6_norm needs h_inf>=0.
    task-397: h_C = h_can/41; P6_norm iff P6_canon.
    These are incompatible unless arch is divided by d or h_inf=0.
    The exact status of C6 normalizedLogVolume on the arch component must be
    arbitrated from Lean definitions before choosing the target. task-399/400.

P6: OPEN. target_accepted=false.