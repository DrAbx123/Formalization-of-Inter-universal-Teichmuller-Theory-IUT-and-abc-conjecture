# C9 smooth P6_norm master: exact chain or exact gap

Task: task-397. Owner: multiradial. Date: 2026-10-25.
Natural-language proof assembly/gap audit only. No Lean/Project edits; no
mixed/E3; no arbitrary data. Deliverable: this file only.
target_accepted=false; P6 open.

## 0. Exact target statement

Fix an admissible initial Theta-datum C (IUT I Def3.1), F_mod=Q, l=41.

Source packet normalization (IUT III Prop3.9/Cor3.12):

    Q_can(C) := -|log q|_packet    (q-pilot, not subject to Ind1/2/3);
    h_can(C) := -|log Theta|_packet (hull of possible Theta-pilot images,
                                     subject to Ind1/2/3).

Corollary 3.12 source inequality:

    Q_can(C) <= h_can(C).                                        (0.1)

C6 normalized convention:

    h_C := h_can(C)/d,   Q_C^norm := Q_can(C)/d,   d=[F_v:Q_p].  (0.2)

In the C9 tame totally ramified type d=e=ell=41. The q-pilot 82-root
normalization gives Q_can=-(b/41)logp, so Q_C^norm=-(b/41^2)logp.

Targets:

    P6_norm:  Q_C^norm <= h_C        for every admissible C.     (0.3)
    P6_canon: Q_can <= h_can = d*h_C.                            (0.4)
    Mixed:    Q_can <= h_C          is FALSE/off by d=41.        (0.5)

P6_norm is the exact statement to assemble. It is equivalent to (0.1) after
dividing both sides by d; no factor 82 enters (the 82-root is already in
Q_can). P6_canon is a different convention; mixed canonical-Q/normalized-h is
invalid.

## 1. Definitions

D1. q-pilot object (IUT III Def3.8(i)): global realified Frobenioid object
determined by q_v at v in V_bad (up to torsion); its packet log-volume is
Q_can=-|log q|.

D2. Theta-pilot object (Def3.8(i)): object determined by theta values
q_v^{j^2}, j in F_l^×; its possible images under the multiradial algorithm are
subject to Ind1/Ind2/Ind3; the holomorphic hull of their union has packet
log-volume h_can=-|log Theta| (Cor3.12 statement).

D3. Multiradial output: collection of possible data in 1,circ U, linked to the
fixed q-pilot input by IPL, expressed by SHE, with APT; HIS permits forgetting
theta functions/values for qualitative logical use (Remark3.11.1(ii)-(iv)).

D4. C6 normalized volume: h_C = h_can/d, Q_C^norm=Q_can/d, d=41; C6
normalizedLogVolume has the 1/D arithmetic-tensor degree division. B_I-zero
arch and procession average are part of the C6/source alignment (N1-N4).

## 2. Step A1: q-pilot input and numerical value

A1 is source-input, not a construction gap:

  A1.1 q-pilot object from q_v (Def3.8(i));
  A1.2 q-pilot F^{value x mu}-prime-strip is fixed/coric input
       (Remark3.11.1(ii));
  A1.3 representation on 1,circ U_Q via 1-column log-Kummer correspondence
       (Step xi-a-c; Remark3.12.2(iv));
  A1.4 output linked to the input by full poly-isomorphisms of
       F^{value x mu}-prime-strips; F^{value} full, F^{unit x mu} subject to
       Ind1/2/3 (IPL; Remark3.11.1(iii); Step xi-b).

Q-pilot numerical value (exact under the C9 82-root calibration):

    q_v = p^{2b} u,  qhat = q_v^{1/82} = pi^b v,  v in 1+pZ_p,
    -|log q|_packet = -(1/82) v_p(q_v) logp = -(b/41) logp.     (2.1)
    b=3: -(3/41)log12301;  b=273: -(273/41)log12301.

A1/Q1 exact gaps:
  - q_v is taken up to torsion; no canonical single q; (2.1) is exact once the
    C9 82-root/unit normalization is fixed (Q1), not an explicit IUT numerical
    formula.
  - The q-pilot input is a poly-isomorphism class, not a canonical section.
  - No E_546-specific complete C/BPS representative is required for universal
    P6_norm.

## 3. Step A2: determinant/log-volume comparison — exact gap

Desired exact equality chain:

    H (holomorphic hull)
      -> rank>1 arithmetic vector bundle E_H over O_{K_v} (1-column)
      -> det^otimes M(E_H) tensor det^otimes M(O(-))^{-1} =: L_H
      -> arithmetic line bundle
      -> normalized degree  deg(L_H)/M = mu_log(H) = h_can.       (3.1)
    q-pilot L_q -> arithmetic line bundle -> normalized degree
      = Q_can in the same scale.                                 (3.2)

If (3.1)-(3.2) hold with the same normalization, A2 is exact: h_can and Q_can
are comparable real numbers in one scale.

Source content:
  - Remark3.9.5(Ob1)-(Ob2): hull stabilized by O_K^times defines local
    arithmetic vector bundle of rank>1;
  - Ob3-1: positive tensor powers of determinant with O(-) inverse;
  - Ob3-2: det^otimes M, M positive sufficiently divisible;
  - Ob3-3: arithmetic degree = log-volume up to normalization;
  - Ob4: det^otimes M output comparable with M-th tensor power of q-pilot;
  - Ob5-Ob9: upper-semi-compatibility, hull approximants, log-Kummer
    vertical-shift rectification, realified semi-simplifications.

SORRY_A2 (exact gap):
  The source does not display the determinant identity (3.1). It explicitly
  leaves the O(-) adjustment details to the reader, does not compute M/weights,
  does not specify normalization factors, and asserts (not proves line-by-line)
  the invariance under tensor-power twists/upper-semi-compatibility and the
  vertical-shift adjustment. Exact missing equalities:
    (A2-1) explicit det^otimes M and O(-)^{-1} exponent/degree identity;
    (A2-2) explicit M and weight normalization;
    (A2-3) deg(L_H)/M = mu_log(H) without unspecified normalization factor;
    (A2-4) tensor-power-twist/upper-semi invariance of normalized log-volume;
    (A2-5) hull-approximant inequality details;
    (A2-6) 1-column log-Kummer vertical-shift rectification identity.
  Therefore A2 is NOT a linear equality chain from the source text; it is a
  conditional theorem with named gap SORRY_A2. No black box is hidden: the gap
  is exactly the unexpanded determinant/normalization identity.

## 4. Step A3: fixed q-pilot value inclusion — exact gap

Desired exact membership:

    Q_can = -|log q| in R_{<= h_can} = {lambda in R | lambda <= h_can}. (4.1)

Source:
  - SHE (Remark3.11.1(iii)): output construction/data simultaneously valid
    relative to the domain Theta-pilot structure and the codomain 1-column
    structure;
  - Step(xi-e): SHE amounts to expressibility under the fixed input pilot
    log-volume -|log q|;
  - Step(xi-f): the construction constitutes a construction (perhaps only up
    to some sort of approximation due to indeterminacies) of the input pilot
    log-volume; hence -|log q| in R_{<= h_can}; therefore Q_can<=h_can.

SORRY_A3 (exact gap):
  The source does NOT state an exact set-membership theorem. It says "perhaps
  only up to some sort of approximation". To make A3 linear, one needs either:

    (A3-exact) Q_can in R_{<= h_can}; or
    (A3-error) an explicit epsilon >=0 with Q_can+epsilon in R_{<=h_can}
               and epsilon sign/bound; then Q_can<=h_can.

  The source supplies neither the exact membership nor a signed error epsilon.
  Also missing: invariance of the normalized pilot log-volume under full
  poly-isomorphisms; SHE-to-membership constitution relation; hull/log-volume
  finiteness. These are SORRY_A3 gaps. No "perhaps up to approximation" is
  accepted as a proof step.

## 5. Step T_norm: exact normalized/canonical factor

Source packet vs C6 normalized:
    h_can = -|log Theta|_packet,   Q_can = -|log q|_packet;
    h_C = h_can/d,   Q_C^norm = Q_can/d,   d=41.                 (5.1)
This is exact under the C6/procession/B_I-zero alignments:
  N1 arch B_I equals the unit ball O_v (both log-volume 0; e adds 1);
  N2 finite reference integral structure O (p_v adds -log p_v);
  N3 procession average over j in F_l^× equals C9 1/m average via ±j pairing;
  N4 global alpha_v/C6 weights equal source normalized weights;
  C1 C9 hull equals source Theta-pilot holomorphic hull;
  C2 C9 q-pilot equals source q-pilot with 82-root normalization.

Under N1-N4/C1-C2, T_norm is exact:
    Q_C^norm = Q_can/d,   h_C = h_can/d.                        (5.2)
Then (0.1) is equivalent to P6_norm Q_C^norm<=h_C. No factor 82; factor d=41.
P6_canon: Q_can<=h_can=d h_C (equivalent to P6_norm). Mixed Q_can<=h_C is
false/off by d.

SORRY_TNORM (exact gap):
  N1-N4/C1-C2 are source-alignment conditions, not notation. C1 (C9 hull =
  source hull) is the main source-object identity; C2 (q-pilot/82-root) is the
  calibration; N1-N4 are normalization/procession/global-weight identifications.
  Without them, h_C/Q_C^norm are C9 quantities, not automatically source
  h_can/Q_can divided by d. Exact missing: C1/C2 and N1-N4.

## 6. Linear conditional proof

Theorem 6.1 (conditional P6_norm). Assume:

  (A1) source q-pilot input/representation (discharged source-input, Q1
       calibration);
  (A2*) the exact determinant identity (3.1)-(3.2), i.e. SORRY_A2 discharged;
  (A3*) the exact membership (4.1), i.e. SORRY_A3 discharged;
  (T*) N1-N4/C1-C2, i.e. SORRY_TNORM discharged.

Then for every admissible C:

    Q_C^norm <= h_C.                                            (6.1)

Proof. A2* gives h_can, Q_can in the same normalized scale. A3* gives
Q_can<=h_can. T* gives Q_C^norm=Q_can/d and h_C=h_can/d. Divide the inequality
by d>0: Q_C^norm<=h_C. C arbitrary => P6_norm universal. QED.

If A3* is replaced by only an approximate inclusion, no proof of (6.1) is
obtained; an explicit signed epsilon is required. If A2* fails, the two
log-volumes are not proved comparable. If T* fails, the factor/object
translation is unproved. Thus the linear proof is conditional exactly on
SORRY_A2, SORRY_A3, SORRY_TNORM.

## 7. Exact gap ledger (no "up to approximation" as proof)

| node | exact statement | status |
|---|---|---|
| A1 | q-pilot input + Q_can=-(b/41)logp | source-input/discharged; Q1 calibration |
| A2 | deg(det^⊗M(E_H)⊗det(O(-))^{-1})/M = h_can; Q_can same scale | SORRY_A2: A2-1..A2-6 missing |
| A3 | Q_can in R_{<=h_can} | SORRY_A3: exact membership or signed epsilon missing |
| T | Q_C^norm=Q_can/41, h_C=h_can/41 | SORRY_TNORM: C1/C2,N1-N4 missing |
| P6_norm | Q_C^norm<=h_C | conditional on A2/A3/T only |
| P6_canon | Q_can<=h_can=d h_C | equivalent to P6_norm; not mixed |
| mixed | Q_can<=h_C | FALSE/off by 41 |

The source's "perhaps only up to some sort of approximation" is a gap, not an
equality; it is marked SORRY_A3, not used as a proof step.

## 8. Why this is not a smooth proof

A smooth proof would require every line to be a definition/equality/exact
inequality. The source supplies:
  - definitions and the qualitative construction (A1);
  - determinant operations/normalization principles (A2), but not the explicit
    identity;
  - SHE/IPL statements (A3), but not exact membership (only approximation
    wording);
  - normalization/procession framework (T), but not C9 object identification.

Therefore the strongest honest statement is Theorem 6.1, conditional on the
three named gaps. No black box remains: each gap has an exact statement and
source location. No arbitrary determinant, region, error, or mixed/E3 profile
is introduced.

## 9. Canonical factor 41 separation

  - P6_norm: Q_C^norm<=h_C. Cor3.12 packets: Q_can<=h_can; divide by d=41.
  - P6_canon: Q_can<=h_can=d h_C. Equivalent to P6_norm.
  - Mixed Q_can<=h_C: would require Q_can<=h_can/41; false in general; the
    only source inequality is Q_can<=h_can. This is the exact factor-41
    separation.
  - Q_can=-b/41 logp includes the 82-root normalization; no factor 82. Full
    q=qhat^82 would add 82 and is not the source q-pilot.

## 10. Consequence / status

Strongest assembled statement: P6_norm for every admissible C, conditional on
SORRY_A2 + SORRY_A3 + SORRY_TNORM. A1 is discharged as source input; Q1
calibration exact. The smooth linear proof is blocked exactly at:
  D1 determinant/normalization identity (A2);
  D2 exact SHE membership or signed error (A3);
  D3 C9/source object and normalization identifications C1/C2,N1-N4 (T).
No explicit complete C is needed for P6_norm; no mixed/E3; no arbitrary data.

No unconditional P6_norm/P6_canon is claimed. No Lean/Project edits.
target_accepted=false; P6 open.

## 11. Acceptance

Only C9-SMOOTH-MASTER-20261025.md written. Natural-language proof/gap assembly
only; no Lean/Project/target edits; no independent review/kernel/comparator
run. target_accepted=false; complete C9/P6 not proved.
