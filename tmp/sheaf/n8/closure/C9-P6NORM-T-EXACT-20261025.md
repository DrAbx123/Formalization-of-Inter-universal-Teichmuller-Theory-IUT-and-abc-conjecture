# C9 exact T_norm / T_canon normalization theorem

Task: task-382 (eliminate named sorry T_norm/T_canon). Owner: qside.
Date: 2026-10-25. Natural-language exact theorem/gap audit; no Lean edits;
no black box; no arbitrary; no mixed/E3; only this file written.

## 0. Verdict

The named sorrys are the C9-specific translation, not a missing IUT III
theorem.  They should be split as:

T_norm (normalization identity):
    c9LogVolume = iiiProcessionNormalizedLogVolume
as functionals on the common target hull / q-pilot objects.

T_canon (canonical-object identity):
    c9TargetHull = iiiHolomorphicHull(union of possible Theta-pilot images),
    c9QPilot     = iiiQPilot(q_v at v in V_bad).

Under T_norm and T_canon, IUT III Corollary 3.12 gives
    c9LogVolume(c9TargetHull) = -|log(Theta)|,
    c9LogVolume(c9QPilot)     = -|log(q)|,
hence h_C >= Q_C and P6.

The exact result is:

- T_norm is **exact at the local level** once the reference integral
  structures coincide: archimedean B_I equals the unit ball O_v (both
  log-volume 0, multiplication by e adds 1); nonarchimedean packet
  normalization uses the integral structure O (log-volume 0, p_v
  multiplication adds -log p_v), and the C9 finite normalization uses the
  same Haar/log integral reference.  The procession average and global
  alpha_v weights must equal the source normalized weights.
- T_canon is **not a theorem of IUT III**: IUT III defines its Theta-pilot
  hull and q-pilot; C9 must identify its abstract target hull/possible-image
  union and native q with those objects.  If the C9 target is instantiated
  as that source hull, T_canon is definitional (no sorry); if C9 keeps an
  abstract target hull, T_canon is an exact gap.

Therefore the named sorry can be eliminated only by the exact C9
instantiation/normalization hypotheses below, not unconditionally from the
source.  The source gap is C1/C2; the normalization gap is N1-N4.

## 1. Exact target statements

Let:
- IIILogVol be the procession-normalized mono-analytic log-volume of
  IUT III Proposition 3.9 (packet normalization + procession average over
  j in F_l^x).
- C9LogVol be the C9 normalized log-volume: B_I-zero reference
  log-volume(B_I)=0, radial h=log r, global weights alpha_v=d_v/[F:Q].
- IIIHull be the holomorphic hull of Remark 3.9.5(i) of the union of possible
  images of the Theta-pilot object (Definition 3.8(i)), subject to
  Ind1/Ind2/Ind3.
- C9Hull be the C9 target holomorphic hull H_C.
- IIIQPilot be the q-pilot object determined by q_v, v in V_bad, and its
  log-volume -|log(q)| (Definition 3.8(i), Corollary 3.12).
- C9QPilot be the C9 native q object with Q_C (uniform value
  Q_p=-(b/41)log p).

T_norm:
    for every common region U,
    C9LogVol(U) = IIILogVol(U).
T_canon:
    C9Hull = IIIHull,
    C9QPilot = IIIQPilot.

Then T_norm + T_canon give the C9 translation
    h_C = C9LogVol(C9Hull) = -|log(Theta)|,
    Q_C = C9LogVol(C9QPilot) = -|log(q)|.

## 2. T_norm: exact local normalization comparison

### 2.1 Archimedean

IUT III Proposition 3.9(i): on each complex archimedean direct summand,
- log-volume of the product integral structure O equals 0;
- multiplication by e=2.71828... adds 1.

C9 B_I-zero:
- log-volume(B_I) equals 0;
- radial log-volume h_v^rad=log r.

If B_I is the unit ball O_v at the complex place (the standard normalization
used in the C9 archimedean assembly), then O_v = B_I and both functionals
coincide exactly:
    C9LogVol_arch = IIILogVol_arch.
The only possible discrepancy is if C9 B_I denotes a different reference
ball (e.g. a scaled log-shell); then an additive constant log lambda appears.
That is N1.

### 2.2 Nonarchimedean

IUT III Proposition 3.9(i):
- packet-normalized log-volume of the local holomorphic integral structure O
  equals 0;
- multiplication by p_v adds -log(p_v).

C9 finite normalized height:
- H_p^Sp is built from the local normalized volume of the finite integral
  structure/log-shell, with the same p-adic Haar normalization;
- global weights alpha_p=d_p/[F:Q].

T_norm is exact at the finite places if:
(N2) the C9 finite reference integral structure is O (not a different
     log-shell or fractional ideal), and
(N3) alpha_v = the source normalized weight N_v at each place.
If only a different reference is used, an additive constant
    C9LogVol = IIILogVol + c
appears; if the reference is a p^m multiple, the constant is -m log p.

### 2.3 Procession average

IUT III Proposition 3.9(i) defines the procession-normalization as the
average of packet-normalized log-volumes over the capsules of the procession;
Corollary 3.12 uses the average over j in F_l^x.

C9 finite row heights H_p^Sp are already the average over the row labels
j=1,...,m=(l-1)/2 (the C9 m rows).  T_norm requires:
(N3) the C9 label index set/weights equal the source F_l^x-procession
     average (including the +/- identification and the C6 alignment).
If C9 averages over a different index set, the equality fails by an explicit
factor/constant.

### 2.4 Global sum

IUT III Proposition 3.9(iii): global log-volume is the sum over places with
all but finitely many zero components, invariant under permutations of A and
equal to the arithmetic degree.

C9 global h_C is the sum of finite bad contributions plus h_inf over
archimedean places with alpha_v=d_v/[F:Q].  T_norm requires:
(N4) the C9 global weight/assembly equals the source global degree/log-volume
     (same alpha_v, same set of places, same C6 alignment).
Then T_norm is exact:
    C9LogVol = IIILogVol.

If N1-N4 hold, T_norm is a definitional identity after unpacking the two
normalizations; no source theorem is missing.  If one of them fails, the
gap is the corresponding explicit additive constant/factor.

## 3. T_canon: canonical-object identity

### 3.1 Hull

IUT III Remark 3.9.5(i) defines the holomorphic hull of U as the smallest
lambda·O region containing U, or the whole IQ if U is not relatively compact.
Corollary 3.12 uses the hull of the union of possible images of the
Theta-pilot object, subject to Ind1/2/3.

C9 H_C is the C9 target holomorphic hull.  For T_canon one must identify:
(C1a) the C9 possible-image union with the source union over j in F_l and
      v_Q in V_Q;
(C1b) the C9 Ind1/Ind2/Ind3 treatment with the source treatment;
(C1c) the C9 hull operation with the source lambda·O hull.
If C9Hull is defined as that source hull, T_canon is definitional.  If C9Hull
is an abstract target field with no such identification, T_canon is an exact
gap: equality is not implied by IUT III.

### 3.2 q-pilot

IUT III Definition 3.8(i)/Corollary 3.12: q-pilot is the object determined by
the q_v at v in V_bad; its log-volume is -|log(q)|, not subject to Ind1/2/3.

C9 native Q_C: Q_p=-(b/41)log p in the uniform profile.  For an actual
q_v=p_v^{2b}, the 2l=82 root normalization gives
    -|log(q)| = -(1/82)log(q_v) = -(2b/82)log p_v = -(b/41)log p_v = Q_p.
Thus:
(C2a) C9QPilot must be the source q-pilot object q_v, not an arbitrary
      auxiliary q;
(C2b) the q-pilot normalization must be the 2l=82 root normalization
      (qhat^{82}=q_v); if raw log(q_v) is used, Q differs by factor 2l.
Under C2a/C2b, T_canon for the q-pilot is exact; otherwise it is a gap.

## 4. Exact conditional theorem

Theorem 4.1 (T_norm/T_canon to P6).  Assume:

(N1)-(N4): T_norm holds as an identity of normalized log-volume functionals;
(C1a)-(C1c): C9Hull equals the source Theta-pilot holomorphic hull;
(C2a)-(C2b): C9QPilot equals the source q-pilot with 2l normalization;
(A1)-(A3): IUT III Corollary 3.12 source schema.

Then for every admissible fixed initial Theta-data/q-pilot input,
    h_C = -|log(Theta)|,
    Q_C = -|log(q)|,
and Corollary 3.12 gives
    Q_C = -|log(q)| <= -|log(Theta)| = h_C,
hence P6 true.

No explicit complete C is constructed; P6 is universal over the fixed
initial Theta-data/q-pilot input.

## 5. If T_norm/T_canon are not exact

Let
    h_C = -|log(Theta)| + c_h,
    Q_C = -|log(q)| + c_q
for additive normalization constants (or errors), and assume T_canon for the
objects.  Corollary 3.12 gives
    -|log(q)| <= -|log(Theta)|
hence
    h_C - Q_C = (-|log(Theta)|+c_h)-(-|log(q)|+c_q)
              >= c_h - c_q.
Thus P6 holds if c_h>=c_q; if c_h<c_q the translation leaves an additive gap.
For multiplicative normalization h_C=d(-|logTheta|), d>0 changes the margin;
d<=0 invalidates the direct inequality.  If T_canon fails, the q-pilot and
hull are different objects and no volume comparison applies.

No such constants are computed by IUT III; they are exactly the C9
normalization data N1-N4/C1-C2.

## 6. Elimination of the named sorry: exact classification

WHAT CAN BE ELIMINATED WITHOUT NEW SOURCE:
- T_norm at the local level, given N1/N2: both sides use the same integral
  structure normalization (arch O=B_I unit ball, nonarch O) and the same
  scaling laws (e -> +1, p_v -> -log p_v).
- T_norm global/procession, given N3/N4: C9 H_p^Sp/C6 averages and
  alpha_v=d_v/[F:Q] equal the source procession/global weights.
- T_canon, if C9Hull and C9QPilot are **definitions** of the source objects
  (source hull/possible images; source q_v).
- The numerical q-pilot identity Q_p=-b/41 under q_v=p^{2b} and 2l=82.

WHAT REMAINS AS EXACT GAP:
(C1) C9Hull is an abstract target object; IUT III does not identify it with
     the source hull.  If C9's target possible-image union/Ind1-3 is different,
     T_canon fails.
(C2) C9QPilot must be the source q-pilot and use the 2l normalization; the
     2l=82 normalization is a C9/source calibration, not an explicit formula
     in IUT III.
(N1) B_I-zero vs source integral structure at archimedean places; exact only
     if B_I is the unit ball O_v.
(N2) C9 nonarch reference integral structure/log-shell vs source O.
(N3) C9 label average vs source F_l^x procession average.
(N4) C9 global alpha_v/C6 vs source normalized global weights.

WITHDRAWN:
- treating T_norm/T_canon as consequences of notation alone;
- eliminating the named sorry by assuming T_norm/T_canon as axioms;
- using raw log(q) instead of the 2l=82 q-pilot log-volume;
- any mixed/E3 profile or explicit C construction.

## 7. Conclusion

The named sorry T_norm/T_canon should be replaced by the exact C9
normalization/object-identification hypotheses N1-N4/C1-C2.  T_norm is exact
at the local normalization level and conditionally exact globally; T_canon is
definitional only when C9Hull/C9QPilot are instantiated as the source objects,
otherwise it is an exact source gap.  Under T_norm+T_canon+A1-A3, P6 follows
universally without explicit C:
    h_C = -|log(Theta)| >= -|log(q)| = Q_C.

There is no black-box citation: the source normalizations and the C9
translation are separated explicitly.  P6 remains conditional on the exact
C9 instantiation/normalization hypotheses; target_accepted=false.

## 8. Sources

- IUT III Definition 3.8, Proposition 3.9, Remark 3.9.5, Theorem 3.11,
  Corollary 3.12 and proof Step (xi): sources/IUT-III.txt SHA256
  822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.
- C9-COR312-THETAPILOT-20261025.md: exact source definitions.
- C9-COR312-TARGET-TRANSLATION-20261025.md: T=h_C=-|logTheta|,
  Q_C=-|logq|; q-pilot 2l=82 match; T1/T2 gaps.
- C9-P6TRUE-SCHEMA-20261025.md: A1-A3 + T schema; G8 translation pending.
- C9-COR312-QPILOT-20261025.md: A1-A3 extraction; translation separate.
- C9-GLOBAL-ASSEMBLY-20261025.md: Q_p=-b/41, alpha_v/C6 weights.
- C9-ARCHIMEDEAN-20261025.md: B_I-zero arch normalization.
