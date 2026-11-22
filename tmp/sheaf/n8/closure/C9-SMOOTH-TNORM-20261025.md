# C9 Smooth T_norm: N1-N4 normalization identities

Task: task-391. Owner: kummer. Date: 2026-10-25.
Natural-language exact identities; no Lean/Project edits; no black box;
no mixed/E3. Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- C9-P6NORM-T-EXACT-20261025.md (task-382), 270 lines,
  SHA256 7d0164a714bceedfecbcdacb4a86ce4c5eb47de18743d2dd5faecbf2c5d7ab96.
- C9-P6NORM-FACTOR-INDEPENDENT-20261025.md, 180+ lines, task-374/382 context;
  procession +/-j pairing.
- C9-ARCH-NORMALIZATION-CORRECTION-20261025.md (task-171), 254 lines,
  SHA256 2174c3ee75fb9dfb83d1bc3e8ef43587f6fbf6d0a1d33538eecc6e0160c769f8.
- C9-TAME-LOG-DOMAIN-20261025.md, 251 lines,
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.
- C9-COR312-IPL-20261025.md, 242 lines,
  SHA256 0c5fd9f3cefe18bfac2eeffe7f6494bca40f21c37dd8118faa6511af3b8b13cd.
- IUT III source text, SHA256
  822e03da7e2a7402a3bb406d698bb3374401e3fb102058c80864d6c06139353d.

## 1. Exact statement

Let:

- IIILogVol be the IUT III procession-normalized mono-analytic log-volume
  (Proposition 3.9 packet normalization and procession average over labels in
  F_l^times);
- C9LogVol be the C9 normalized log-volume (B_I-zero arch reference; finite
  O reference; global alpha_v weights);
- IIIHull be the holomorphic hull of the union of possible images of the
  Theta-pilot object under Ind1/Ind2/Ind3;
- C9Hull be the C9 target holomorphic hull H_C;
- IIIQPilot be the q-pilot object determined by q_v, v in V_bad;
- C9QPilot be the C9 q-pilot/native q object.

N1: archimedean reference B_I = O_v.
N2: C9 finite reference integral structure = source O (not a different
    log-shell/fractional ideal).
N3: source procession average over F_l^times = C9 1/m average over j=1,...,m
    with +/-j pairing, m=(l-1)/2, no extra 1/2.
N4: C9 alpha_v/C6 weights = source normalized weights.

Theorem 1.1 (T_norm). Under N1-N4 and the object identifications
C9Hull=IIIHull, C9QPilot=IIIQPilot:

    h_C = C9LogVol(C9Hull) = IIILogVol(IIIHull) = -|log Theta|,
    Q_C = C9LogVol(C9QPilot) = IIILogVol(IIIQPilot) = -|log q|.     (1.1)

If one of N1-N4 fails, the discrepancy is the explicit constant/factor in
Sections 3-6, not an unspecified error.

## 2. What is proved and what is conditional

Proved/definitional after matching the source normalizations:

- N1 under the standard C9 archimedean identification B_I=O_v (unit ball);
- N2 under the C9 finite O-reference normalization used in the TAME/N1
  formulas;
- N3 exactly, by the +/-j pairing and uniform weights;
- N4 at the weight-definition level alpha_v=d_v/[F:Q], with the C6
  provenance/row alignment as an explicit conditional input.

Conditional/gap:

- N1 if C9 B_I is a scaled ball lambda O_v: additive global constant;
- N2 if C9 finite reference is J=pi O or p^m O: additive finite constant;
- N4 if C6 weights differ from source normalized weights: explicit ratio/
  additive constant;
- T_norm also needs the object identifications C9Hull=IIIHull and
  C9QPilot=IIIQPilot; those are T_canon, not normalization identities.

## 3. N1: archimedean B_I = O_v

IUT III Proposition 3.9(i) normalization at a complex archimedean place:

- product integral structure O_v has log-volume 0;
- multiplication by e=2.71828... adds 1.

C9 B_I-zero convention: log-volume(B_I)=0; radial readout h_v^rad=log r.

If B_I is the unit ball O_v at the complex place, then both functionals have
the same reference and the same multiplication law; hence

    C9LogVol_arch = IIILogVol_arch.                                (3.1)

This is the standard C9 archimedean assembly identification: B_I is the
unit-ball integral structure, not a log-shell radius pi.

If instead B_I = lambda O_v (scaled reference ball), then the difference is

    C9LogVol_arch = IIILogVol_arch + log lambda                (3.2)

per complex place, and after global weights:

    h_inf difference = (1/[F:Q]) sum_{v|infty} d_v log lambda. (3.3)

N1 holds exactly iff lambda=1. The frozen C9 B_I-zero convention uses
lambda=1; no arbitrary scaling is introduced.

## 4. N2: finite reference O

IUT III Proposition 3.9(i) finite normalization:

- packet-normalized log-volume of local holomorphic integral structure O is 0;
- multiplication by p_v adds -log p_v;
- for pi_v with pi_v^e=p_v u, log|pi_v|=-1/e log p_v.

C9/TAME finite row values (N1 file, TAME section6):

    nu_A/log p = -s-1/e,
    nu_B/log p = -s+(r-1)-r/e.                                  (4.1)

Check against O-reference:

    L_A = p^s pi_i D_r,
    logvol(L_A)/log p = -s -1/e;                                (4.2)
    L_B = p^{s-r+1} J^{tensor r}, J=pi O,
    logvol(L_B)/log p = -(s-r+1)-r/e = -s+(r-1)-r/e.            (4.3)

These are exactly (4.1). Thus the C9 finite row normalization uses the same
O reference and the same p_v/pi_v normalization as the source; N2 holds
exactly for the TAME/N1 row formulas.

If C9 used a different finite reference:

- reference J=pi O gives an additive -1/e log p per factor;
- reference p^m O gives an additive -m log p;
- reference I=p^{-1}J gives an additive +(1-1/e)log p.

N2 is exact under the O reference; otherwise the explicit constants above
appear.

## 5. N3: procession average and +/-j pairing

IUT III Proposition 3.9(i): procession normalization is the average of
packet-normalized log-volumes over the capsules/labels of the procession;
Corollary 3.12 uses labels in F_l^times.

C9 finite row heights use the average

    1/m sum_{j=1}^m,   m=(l-1)/2=(41-1)/2=20,   l=41.            (5.1)

The source label set F_l^times has l-1=40 elements. The theta value labels
occur in pairs +/-j because q^{j^2}=q^{(-j)^2}. If the source average is
uniform over F_l^times, pair each j=1,...,m with -j:

    (1/40) sum_{j in F_l^times} f(j)
      = (1/40) sum_{j=1}^m (f(j)+f(-j))
      = (1/20) sum_{j=1}^m f(j)                                 (5.2)

for any function f(j)=f(-j), in particular for the theta/q row heights.
Therefore the source F_l^times average equals the C9 1/m average; no extra
1/2 appears. N3 holds exactly, provided the C9 label set is the same
F_l^times with +/- pairing (C6 alignment).

If the source used a different label set or nonuniform weights, the
discrepancy is the explicit weighted average difference; if one used all
40 labels but C9 20 without pairing, the factor is 2. The +/- pairing removes
the factor 2 exactly.

## 6. N4: alpha_v/C6 weights = source normalized weights

IUT III Proposition 3.9(iii): global log-volume is the sum over places, with
all but finitely many zero components, invariant under permutations of A,
and equal to the arithmetic degree.

C9 global weights:

    alpha_v = d_v/[F:Q],  sum_{v|infty} alpha_v=1,                (6.1)
    h_inf = sum_{v|infty} alpha_v log r_v.                        (6.2)

For F=Q: d_v=1, alpha_inf=1, h_inf=log r_inf. This matches the standard
normalized arithmetic-degree weight d_v/[F:Q] for archimedean places.

At finite places the source degree weight is 1/[F:Q] times the local
log-residue term; C9 alpha_p=d_p/[F:Q] is the corresponding normalized
weight. Thus N4 is exact at the **definitional weight level**: both sides
use the arithmetic degree normalized by [F:Q], with archimedean d_v and
finite local degree weights.

The conditional part is the C6 provenance/row/place alignment: that the C9
target has the same set of places, the same row labels, and the same
permutation action as the source procession. This is a separate object-level
identification, not a new numerical normalization. If C6 weights differ from
the source normalized weights by a factor c_place, the exact error is

    h_C - (-|log Theta|)
      = sum_places (c_place-1) w_place log r_place,             (6.3)

or the corresponding additive constant if the difference is a shift.

N4 holds exactly once C6 alignment is identified with the source normalized
weights; without C6, the numerical weight identity is conditional.

## 7. Conclusion

Under N1-N4 and the object identifications C9Hull=IIIHull,
C9QPilot=IIIQPilot:

    h_C = -|log Theta|,
    Q_C = -|log q|,

exactly. The identities are:

- N1: archimedean B_I=O_v, exact with lambda=1;
- N2: finite O-reference, exact by matching the TAME row formulas;
- N3: F_l^times average equals C9 1/m average by +/-j pairing, exact;
- N4: alpha_v=d_v/[F:Q] matches the normalized source weight, exact at the
  weight level; C6 provenance/alignment is the remaining object-level
  conditional.

If any normalization reference is changed, the exact constants are those in
Sections 3-6: log lambda for B_I scaling, -1/e log p for J=pi O,
-m log p for p^m O, factor 2 for unpaired 40-vs-20 labels, and the weighted
difference (6.3) for C6 weight mismatch. None is an arbitrary parameter.

No black box: N1-N4 are unpacked into the source normalization laws and the
C9 row/average formulas. No mixed/E3 profile is used.

## 8. Status

- Natural-language exact normalization theorem only; no Lean/Project edits.
- N1-N4 identities proved under the stated references; exact constants for
  failures recorded; T_canon object identity remains separate.
- target_accepted=false; P6 open.
