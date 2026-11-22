# C9 canonical P6_can master

Task: task-406. Owner: multiradial. Date: 2026-10-25.
Natural-language proof assembly only. No normalized surrogate; no black box;
no mixed/E3; no arbitrary data; no Lean/Project edits. Deliverable: this file
only. target_accepted=false; P6 open.

## 0. Canonical target

Source packet normalization (IUT III Prop3.9/Cor3.12):

    Q_III := -|log q|_packet,
    H_III := -|log Theta|_packet,
    Cor3.12: Q_III <= H_III.                                     (0.1)

C9 canonical convention (C9Paper):

    Q_C^canon := localSignedLog(qCandidate),
    h_C^canon := C9 canonical hull log-volume (no 1/d division).
    P6_can: Q_C^canon <= h_C^canon.                             (0.2)

P6_can is the canonical inequality, not the normalized surrogate. The
normalized convention Q_C^norm=Q_III/d, h_C^norm=H_III/d, d=41, is a different
target; it is not used here. Mixed Q_canon with h_C^norm is off by 41 and is
excluded.

## 1. Canonical q-pilot value

Under the C9 canonical 2l=82 root normalization:

    q_v = p^{2b} u,  qhat = q_v^{1/82} = pi^b v,  v in 1+pZ_p,
    Q_III = -(1/82) v_p(q_v) logp = -(b/41) logp.                 (1.1)
    b=3: -(3/41)log12301; b=273: -(273/41)log12301.

This is the canonical source packet q-log, including the 82-root and the
degree-41 denominator; no factor 82 or 41 remains beyond the displayed formula.
The numerical identity is exact once the C9 canonical 2l=82 normalization is
fixed (Q1 calibration); IUT III does not display this local numerical formula.

## 2. A1 canonical q-pilot input/representation

A1 is source-input:

  A1.1 q-pilot object from q_v (IUT III Def3.8(i));
  A1.2 fixed/coric q-pilot F^{value x mu}-prime-strip (Remark3.11.1(ii));
  A1.3 1-column representation on 1,circ U_Q (Step xi-a-c;
       Remark3.12.2(iv));
  A1.4 output-to-input full poly-isomorphism link (IPL, Remark3.11.1(iii);
       Step xi-b).

A1 does not construct an E_546-specific complete C/BPS representative; it is
the universal source situation. The only A1 numerical input is Q_III in (1.1),
with the Q1 calibration gap: q_v is up to torsion and IUT III does not state
the explicit 1/82 formula.

## 3. A2 canonical determinant/log-volume comparison

Desired canonical equality:

    H_III = normalized arithmetic degree of
            det^otimes M(E_H) tensor det^otimes M(O(-))^{-1} / M,  (3.1)
    Q_III = canonical q-pilot arithmetic degree/log-volume,       (3.2)
    with both in the same canonical packet normalization.

Source content: Remark3.9.5(Ob1)-(Ob9); Prop3.9; Step(xi-c),(xi-d):
  - hull -> rank>1 arithmetic vector bundle E_H over 1-column local rings;
  - positive tensor power of determinant with O(-) inverse;
  - det^otimes M, M positive sufficiently divisible;
  - arithmetic degree = log-volume up to normalization;
  - q-pilot comparison;
  - upper-semi-compatibility, hull approximants, log-Kummer vertical-shift
    rectification.

SORRY_A2 (exact gap):
  The source does not display (3.1)-(3.2) as an equality. Exact missing:
   (A2-1) explicit det^otimes M and O(-)^{-1} exponent/degree identity;
   (A2-2) explicit M and weight normalization;
   (A2-3) deg/M = H_III with no unspecified factor;
   (A2-4) tensor-power-twist/upper-semi invariance;
   (A2-5) hull-approximant inequality;
   (A2-6) 1-column log-Kummer vertical-shift rectification.
  A2 is conditional on A2-1..A2-6; no black box is hidden.

## 4. A3 canonical fixed q-pilot value/SHE membership

Desired canonical membership:

    Q_III in R_{<=H_III} = {lambda in R | lambda <= H_III}.       (4.1)

Source: SHE (Remark3.11.1(iii)); Step(xi-e): SHE expresses output while the
input pilot log-volume is fixed to Q_III; Step(xi-f): construction includes the
input pilot log-volume (up to indeterminacy approximation), hence Q_III in
R_{<=H_III}; therefore Q_III<=H_III.

SORRY_A3 (exact gap):
  The source says "perhaps only up to some sort of approximation"; it does not
  state exact membership (4.1), nor a signed error epsilon with
  Q_III+epsilon in R_{<=H_III} and epsilon>=0 (or a proved bound). Also
  missing: full-poly-isomorphism invariance of the normalized pilot
  log-volume, SHE-to-membership constitution, hull/log-volume finiteness.
  A3 is conditional on exact membership or a signed epsilon; approximation
  wording is not a proof step.

## 5. T_can: canonical-object identity

T_can is the exact C9-to-source canonical identification:

  Object/hull:
   (C1a) C9 possible-image union = source union over j in F_l^×, v_Q in V_Q;
   (C1b) C9 Ind1/Ind2/Ind3 treatment = source treatment;
   (C1c) C9 hull operation = source lambda·O holomorphic hull.
  q-pilot:
   (C2a) C9QPilot = source q-pilot q_v, not an arbitrary auxiliary q;
   (C2b) 2l=82 root normalization qhat^82=q_v.
  Volume:
   (N1) arch B_I = source unit ball O_v (log-volume 0, e -> +1);
   (N2) finite reference = source O (p_v -> -log p_v);
   (N3) C9 label/procession average = source F_l^× average with ± pairing;
   (N4) C9 global alpha_v/C6 weights = source normalized global weights.

Under C1a-c, C2a-b, N1-N4, the canonical C9 log-volume equals the III packet
log-volume:

    C9LogVol(C9Hull) = H_III,
    C9LogVol(C9QPilot) = Q_III.                                  (5.1)

Then T_can gives exact:
    h_C^canon = H_III,   Q_C^canon = Q_III.                      (5.2)

SORRY_TCAN (exact gap):
  IUT III defines its Theta-pilot hull/q-pilot but does NOT identify an abstract
  C9 target hull/native q with them. If C9 defines C9Hull/C9QPilot as those
  source objects and uses the same canonical volume functional, T_can is
  definitional. If C9Hull/C9QPilot are abstract objects, T_can is an exact gap.
  C1a-c/C2a-b/N1-N4 are the exact identification hypotheses; they are not
  consequences of notation.

## 6. Canonical proof

Theorem 6.1 (conditional P6_can). Assume:

  A1 (source q-pilot input; Q1 canonical value);
  A2 (canonical determinant/log-volume equality (3.1)-(3.2));
  A3 (canonical exact membership (4.1));
  T_can (C1a-c, C2a-b, N1-N4).

Then for every admissible C:

    Q_C^canon <= h_C^canon.                                     (6.1)

Proof. A2 gives H_III,Q_III in the same canonical scale. A3 gives
Q_III in R_{<=H_III}, hence Q_III<=H_III. T_can gives
Q_C^canon=Q_III and h_C^canon=H_III. Therefore Q_C^canon<=h_C^canon. C
arbitrary => universal P6_can. QED.

No normalized division is used: the canonical inequality is direct. If A3 is
replaced by an approximation without a signed epsilon, (6.1) is not proved.
If A2 fails, H_III/Q_III are not proved comparable. If T_can fails, the C9
canonical objects are not the source objects and no volume comparison applies.

## 7. Exact gaps

SORRY_A2: A2-1..A2-6 exact determinant/O(-)/M/degree=log-volume/tensor-twist/
upper-semi/hull/vertical-shift equalities. Source leaves O(-) details, does not
display the identity.

SORRY_A3: exact membership Q_III in R_{<=H_III} or signed epsilon with
Q_III+epsilon in R and epsilon sign/bound; source only "perhaps up to
approximation".

SORRY_TCAN: C1a-c hull/possible-image identity, C2a-b q-pilot/82-root identity,
N1-N4 normalization/procession/global-weight identity. If C9 target/hull/q are
defined as source objects, T_can is definitional; otherwise exact gap.

Q1/A1: Q_III=-(b/41)logp exact under 82-root canonical calibration; q_v up to
torsion/no explicit numerical formula in IUT III. A1 source-input otherwise.

No other gaps. No normalized surrogate; no mixed/E3; no arbitrary data.

## 8. Canonical vs normalized (factor 41 separation)

  - Source canonical: Q_III=-(b/41)logp, H_III; Cor3.12 Q_III<=H_III.
  - Canonical C9 (this file): Q_C^canon=Q_III, h_C^canon=H_III; P6_can direct.
  - Normalized C9: Q_C^norm=Q_III/41, h_C^norm=H_III/41; P6_norm equivalent.
  - Mixed Q_canon with h_C^norm: would require Q_III<=H_III/41; false in
    general; exact factor 41.
  - Raw log(q_v) (not qhat 82-root) differs by factor 82 and is not the
    canonical q-pilot.

P6_can is not obtained from P6_norm by an unproved normalization surrogate;
it is the direct canonical source inequality conditional on T_can/A2/A3.

## 9. Status

Strongest assembled statement: P6_can for every admissible C, conditional on
A2, A3, and T_can; A1/Q1 discharged as source input/calibration. No smooth
unconditional proof: SORRY_A2, SORRY_A3, SORRY_TCAN remain exact gaps. No
explicit complete C is required. No normalized surrogate, no mixed/E3, no
arbitrary data, no Lean/Project edits. target_accepted=false; P6 open.

## 10. Acceptance

Only C9-CAN-MASTER-20261025.md written. Natural-language proof/gap assembly
only; no Lean/Project/target edits; no independent review/kernel/comparator
run. target_accepted=false; complete C9/P6 not proved.
