# S741 memo (task J): optimal transport / entropy / Brunn-Minkowski / information geometry for the paper log-volume inequality

Date: 2026-10-30. Task J. **Research memo only.** No Lean file added or
edited, no target changed, no proof claimed.  target_accepted = false.

Inputs read: TASK_LEDGER.md, FROZEN_TARGET.md, FINAL_PAPER_LEVEL_GAP.md,
FIVE_PAPER_GAPS_STATUS.md, CURRENT_PATH_NOTES.md,
ProcessionNormalizationWeightsActual.md, GlobalQPilotNormalization.md,
ThetaHullAveragingOrderAnalysis.md, S702_QPilotRegionNorm_LP_MEMO.md,
tmp/sheaf/n8/closure/C9-NEW-OPTIMAL-TRANSPORT-20261025.md, the Lean files
listed in section 2, and IUT III / IUT IV corpus extracts
(tmp/source-extract/iut3.txt, iut4.txt).  Line numbers below are corpus line
numbers of those extracts.

---

## 0. Verdict (short)

**REJECT** optimal transport, entropy/information theory, Brunn-Minkowski and
information geometry as *proof routes* for

    -|log(Theta)| >= -|log(q)|     (Cor 3.12; Lean: qPilotLogVolume <= signedHullLogVolume)

for five independent reasons (developed in sections 3-6):

* **V1 (no inequality content).** In the paper the inequality is derived
  *formally* from a **down-set membership**: R_{<= -|log Theta|} := {lam | lam
  <= -|log Theta|} (IUT III 11028-11030) and "-|log q| in R_{<= -|log Theta|}"
  (11074-11084, "then follows formally"; 11401 "essentially formally").  The
  only measure-theoretic inputs are monotonicity of the log-volume under
  inclusion and finiteness.  There is no numerical gap to estimate.
* **V2 (no common ambient space).** An OT/entropy statement needs one
  measurable space carrying both the q-pilot region and the Theta-hull.  The
  0-column and 1-column arithmetic holomorphic structures are deliberately
  alien; the Theta x mu-LGP link is a full poly-isomorphism, i.e. a *set* of
  isomorphisms (the (Ind1),(Ind2),(Ind3) indeterminacy), not a map.  Any
  "common carrier" is a fabricated object.
* **V3 (no canonical probability on the indeterminacy set).** "Possible
  images" is a *set* of objects, not a law.  Putting a measure/distribution on
  it is an arbitrary choice = surrogate.
* **V4 (wrong direction).** OT / Brunn-Minkowski / EPI / DPI are lower-bound
  machines for volumes of sums, coarse-grainings and couplings.  The target is
  an upper bound on the volume of a hull of a union.  Section 6 proves that no
  uniform upper bound of that shape exists in this carrier.
* **V5 (sharpness).** The constant 1 cannot be improved (IUT III (xi-h)
  11139-11149 + IUT IV Remark 2.3.2(ii) 3277-3285), and the N-th-power
  variants are false.  A boundary-constant inequality cannot come from an
  estimate with slack; any OT/BM/entropy argument would produce a bound with a
  constant or an error term, i.e. a strictly different statement.

**What survives** (the only paper-faithful residue, section 7): the
order-theoretic/closure content of IUT III Remark 3.9.5, which the paper
itself calls an adjoint / canonical splitting / integration operation
(7835-7838), and which is already encoded in Lean as
IQHullLogVolumeInterface.imageSet_logVolume_le_hull and hullLogVolumeRay =
Set.Iic.  This is not optimal transport and adds no new inequality.

**Answer to "does it keep the actual q/Theta objects?": no.**  Every genuine
OT/entropy instantiation requires (a) a replacement carrier, (b) a reference
probability, (c) a coupling/kernel, or (d) an extra variational structure on
the indeterminacy set.  The only statement that keeps the actual objects is
the trivial mu_log(P) <= mu_log(phi(P)) for P <= phi(P) with mu_log monotone.

---

## 1. The inequality as the paper states and derives it

### 1.1 Statement and sign

IUT III 10499-10529: -|log(Theta)| is the *procession-normalized mono-analytic
log-volume* (average over j in F_l^x) of the **holomorphic hull** of the
**union of possible images** of a Theta-pilot object, relative to the Kummer
isomorphisms, in the multiradial representation, **subject to**
(Ind1),(Ind2),(Ind3).  -|log(q)| is the same kind of log-volume of the image of
a **q-pilot object**, **not** subject to (Ind1)-(Ind3).  Conclusion:

    -|log(Theta)| in R,     -|log(Theta)| >= -|log(q)|
    i.e. C_Theta >= -1 for any C_Theta with  -|log(Theta)| <= C_Theta |log q|.

WLOG (10530-10534): if -|log(Theta)| >= 0 the result is immediate, so the hard
case is -|log(Theta)| < 0; in that case the hull is a proper lam*O.

### 1.2 The derivation is a membership in a down-set

* (xi-d), 11008-11030: after forming the hull and applying the log-volume one
  gets two comparable objects: R_{<= -|log(Theta)|} := {lam in R | lam <=
  -|log(Theta)|} subset R together with -|log(q)| in R, where -|log(Theta)| is
  *by definition* the (negative) log-volume of 1,circ U, and -|log(q)| is the
  log-volume of the region arising from the representation of the q-pilot
  object at (1,0) on 1,circ U_Q.
* (xi-e), 11049-11073: the constructed possible output log-volumes all lie in
  that down-set; "expressibility relative to the 1-column" means precisely
  that the pilot-object log-volume of the input data is the fixed value
  -|log(q)|.
* (xi-f), 11074-11084: hence "-|log q| in R_{<= -|log(Theta)|}", "hence also
  the inequality ... then follows formally".
* (xi-g), 11085-11089: Fig. 3.8 - the two computations of the log-volume of the
  q-pilot object are "tautologically equivalent".

**Why all possible output log-volumes are <= -|log(Theta)|:** each possible
image is a subregion of the hull 1,circ U_{j,vQ} and the log-volume is
monotone under inclusion.  That is the entire volume-theoretic content.

### 1.3 The paper's own abstract form of this, and its sharpness

* Remark 3.9.5(i), 7787-7809: the holomorphic hull is **the smallest subset of
  the form lam*O containing U** (and IQ((-)) itself if U is not relatively
  compact).
* Remark 3.9.5(ii), 7811-7838: the hull operation phi : P -> H is
  characterized by (P1) phi(H) = H, (P2) P subset phi(P), (P3) monotonicity,
  and is phi(P) = intersection over H superset P of H; the paper calls it "a
  sort of adjoint, or push forward in the opposite direction, of the inclusion
  H subset P", "a canonical splitting of the inclusion", "a sort of
  integration operation" (7835-7838).
* Remark 3.9.5(iii), 7845-7867: Phi(P) := {H in H | phi(P) superset H,
  mu_log(phi(P)) >= mu_log(H) >= mu_log(P)}, Xi(P) = the equality case,
  H_Phi(P) = union Phi(P); these are the "log-volume hull-approximants".  A
  compactness statement (7870-7880) bounds the indeterminacy of the choice.
* Remark 3.9.5(iv), 7881-7911: phi(P) in Phi(P), i.e.
  **mu_log(P) <= mu_log(phi(P))**, and this can be strict; Xi(P) nonempty is
  *not* automatic ((Xi1): residue degree 1 / existence of a Z_p-submodule Q
  with mu_log(Q) = mu_log(P); (Xi2): archimedean v_Q).  The paper's own strict
  example (7913-7938) is two-dimensional: I = Q_p x Q_p, H_0 = Z_p x Z_p,
  H_1 = p^{-1}Z_p x pZ_p, P = H_0 union ({p^{-1}} x Z_p), H_P = p^{-1}Z_p x Z_p,
  and mu_I(P) = 1 < 2 - p^{-1} = mu_I(H_0 union H_1).
* Remark 3.12.1(i), 11176-11178: **explicit upper bounds** on -|log(Theta)|
  (the C_Theta estimates) are the business of IUT IV, *not* of Cor 3.12.
* Remark 3.12.1(ii), 11179-11210: for generalized links
  q^lam |-> q^{(1,2,...,(l*)^2)} the same argument gives C_Theta >= -lam,
  sharper for lam < 1.
* Step (xi-h), 11139-11149 + IUT IV Remark 2.3.2(ii), 3277-3285: the analogue
  for N-th tensor powers "would lead to sharper inequalities", and these are
  **known to be false**; the constant 1 "cannot be improved".
* Remark 3.12.2(ii), 11257-11276: the paper's own summary of the *mechanism*:
  the multiradial representation lets one compute/estimate **value-group
  portions in terms of unit-group portions**; "it is precisely these estimates
  that give rise to the inequality".  This is a *structural* transfer
  (log-Kummer correspondence), not a measure-theoretic inequality.

**Consequence for task J.**  The target is a membership statement in an
order-theoretic down-set, obtained from (i) q-region subset Theta-hull (or its
log-volume being a possible output log-volume) and (ii) monotonicity.
Everything else in Cor 3.12 is bookkeeping/definition.  Any tool that proves
*inequalities between volumes of two objects* is proving a different statement.

---

## 2. Faithful Lean transcription (state of the repository)

* tmp/sheaf/xif/PaperSignedHull.lean: PaperSignedHull carries
  ambient : IQHullLogVolumeInterface X, a finite procession : WeightedValues
  label, a hull : FiniteHull label, and the exact normalization obligation
  hull_logVolume_eq_average : ambient.logVolume ambient.hull =
  ENNReal.ofReal procession.average, with 0 <= average.  Then
  signedHullLogVolume := -(ambient.logVolume ambient.hull).toReal = -average,
  and signedHullLogVolume_nonpos.
* LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean:
  IQHullLogVolumeInterface has exactly imageSet subset hull, a monotone
  logVolume : Set X -> ENNReal, a unit region with finite log-volume, and
  logVolume (scaleShift '' unitRegion) <= logVolume unitRegion.  Proved:
  imageSet_logVolume_le_hull, hull_logVolume_lt_top, lower_bound_and_finiteness.
  This *is* Remark 3.9.5(ii)(iii) in Lean form.
* tmp/sheaf/xif/PaperXiFInclusion.lean: the target is
  link_implies_inclusion : link_identification ->
  O.qPilotLogVolume in hullLogVolumeRay P.signedHullLogVolume, and
  hullLogVolumeRay = Set.Iic (cf. ConcreteSourceComparisonActual.lean line 20),
  i.e. **literally the paper's R_{<= -|log(Theta)|}**.  The four
  PaperXiFSourceLink fields are the remaining obligations.
* Proved model inequality (PaperLevelXiFTargetProofActual.lean):
  globalQPilotLog_le_globalThetaHullLog, per b from
  qPilotNormRegion subset rootNormHull (RootNormalizedContainmentActual.lean,
  RootHullContainmentInequalityActual.lean) plus
  arithmeticTupleNormalizedLogVolume_mono.  The containment uses the label
  j = +-1 (gaussExponent_oneLabel) where the root exponent is j^2 = 1, and
  rootHalfCoefficient = c_norm/(2l) <= c_norm.
  Normalized log-volume
  arithmeticTupleNormalizedLogVolume = (1/finrank)*(log (mu S) - log (mu
  O_canonical)) (FinitePlaceNormalizedUnitScalingLogVolume.lean), with
  mu_log O_canonical = 0.
* S726PaperHullVsS663GapActual.lean: paperPerBThetaHullLog <= 0 but the S663
  magnitude average is > 0, hence PaperHullVsS663ThetaAverageGap is **false**.
  So the "average of point magnitudes" (S663 route) can never be the paper
  hull log.  This also kills every "entropy of the distribution of theta
  values" idea (section 4.1).
* S716PaperThetaHullLogSourceAuditActual.lean,
  S733CorrectedPaperFinalCor312Actual.lean: the paper hull log is
  paperPerBThetaHullLog = perBThetaHullLog = rootThetaHullLog with coefficient
  c_norm/(2l), and S733CorrectedHullLog :
  P.signedHullLogVolume = -paperPerBThetaHullLog T b is the intended
  identification (currently a hypothesis hP).
* q side: paperQPilotLogVolume C3 = localSignedLog C3.q = Real.log ||C3.q.q||
  < 0 (PaperQPilotLogVolume.lean); the model per-b scalar is
  qPilotClassicalLog = -(sum_i c_norm i) * log p.
* q[2u]/root stack: S356RootStackActionGroupoidActual.lean gives the
  non-degenerate action groupoid (objects = candidate 2l-th roots, morphisms =
  mu_{2l}, **no quotient**), and the exact missing RootStackMonoidSectionCarrier
  with qSection_toCompletion qSection = (qVFam T b).q and
  rootSection^(2l) = qSection.

**Reading of the current exact gap.**  It is not "prove an inequality between
two volumes".  It is:

    (G1) the q-pilot's log-volume is realized as one of the possible output
         log-volumes of the Theta-pilot construction (structural; the paper's
         (IPL)+(SHE)+Fig. 3.8), equivalently a containment
         q-pilot region subset Theta-hull at the actual carrier;
    (G2) logVolume is monotone (already proved, both in the interface and in
         the model);
    (G3) the q[2u]/root-stack normalization is the correct one on both sides
         (|log q[2u]| = |log q[1u]|/(2l); c_root = c_norm/(2l)).

OT/entropy/BM touch none of (G1)-(G3).

---

## 3. Optimal transport

### 3.1 What an OT proof would have to be

The standard template: two probability measures mu, nu on a common Polish space
X, a cost c, the set Pi(mu,nu) of couplings, Kantorovich duality, and an
inequality proved by (i) choosing a plan, (ii) applying a displacement-convexity
/ Jacobian estimate.  Every ingredient is a hypothesis to be discharged.

### 3.2 (O1) There is no common measurable space

q-pilot and Theta-pilot live in the 0-column and 1-column Theta^{+-ellNF}-Hodge
theaters; the Theta x mu-LGP-link is a **full poly-isomorphism** of
F^{models x mu}-prime-strips (IUT III 10605-10629), i.e. a *set* of
isomorphisms modulo (Ind1),(Ind2),(Ind3).  The paper's whole point is that
there is no canonical identification; that is why the argument must be
"tautological" (11085-11089).  Choosing **one** isomorphism to build a common
space is exactly the kind of choice the indeterminacies forbid - and it would
be an unproved extra structure.  Remark 3.12.2 also stresses that the two
structures are distinguished from one another; a transport between them is not
available.

### 3.3 (O2) There is no canonical probability on the possible images

The normalized log-volume is a **valuation on regions**: in Lean,
(1/d)*(log mu(S) - log mu(O)), a Haar measure normalized against the canonical
unit reference.  It is *not* an integral against a probability.  The set of
possible images is a set of *indeterminacies*, and nothing in the source gives
a measure on it (the paper makes the indeterminacy *compact*, 7870-7880, not
*measured*).  Any choice of weights on the possible images is arbitrary, hence
a surrogate - the same failure mode the project already rejected for the S663
/ raw SignedLabel averages.

### 3.4 (O3) Orientation: transport is at best equivalent to the containment

Sign lemma: let T : X_Theta -> X_q be measurable with T_* mu_Theta = mu_q and
mu_log(T(E)) <= mu_log(E) for all relevant E.  Then
mu_log(q-region) <= mu_log(Theta-hull) - the target, but only *because the map
is onto the q-region and non-increasing*.  Conversely, if the containment
q-region subset Theta-hull is available, the target follows by monotonicity
alone, with no map at all.  Hence:

* an OT proof is **never weaker** than the containment and **cannot replace**
  it: the existence of T with the required image is a strictly stronger
  hypothesis than the containment;
* the *natural* direction (Theta-image -> q) is a map whose image is the
  q-pilot region only in the paper's tautological sense, i.e. only *after* the
  structural identification (G1) is known.

This is consistent with the earlier n8 memo
(tmp/sheaf/n8/closure/C9-NEW-OPTIMAL-TRANSPORT-20261025.md, section 0, Lemmas
2.1-2.3), which found the *opposite* sign for a contracting transport.
Reconciliation: that memo analyzed a *transport between two measures*; the
paper's relation is an **inclusion** (or a value identification).  Inclusion
gives the target immediately; a contraction-type transport gives its negation.
So the OT framing does not merely fail to help - it mis-orients the problem.
(The C9 memo's conclusion "the transport program is a negative result, not a
P6 proof" stands; its P6 is the same inequality in the opposite sign
convention.)

### 3.5 (O4) Kantorovich duality gives no mass inequality

W_1(mu,nu) <= C controls displacement, not total mass; duality is sup over
potentials = inf over plans of int c d pi.  There is no cost function in IUT
III section 3.12 at all, so there is nothing to dualize.

**Verdict section 3: REJECT.**  Concrete theorems considered and refused:
Birkhoff-von Neumann / Hardy-Littlewood-Polya (needs a common ordered space),
Brenier/Monge-Ampere (needs a Riemannian/measure-theoretic structure and
regularity), Kantorovich duality, displacement convexity (needs geodesic
convexity of the functional), Caffarelli contraction (needs Gaussian reference
measures).  None has its hypotheses available, and all would change the
objects.

---

## 4. Entropy and information theory

### 4.1 The entropy reading is a tautology, not a tool

For a region A with 0 < mu(A) < infinity, let U_A be the normalized Haar (=
uniform) probability on A.  Its differential entropy w.r.t. Haar is
H(U_A) = log mu(A).  Hence

    -mu_log(hull) = (1/d)*(log mu(O) - log mu(hull))
                  = (1/d)*(log mu(O) - H(U_hull)),

so the target |log Theta| <= |log q| is *literally*

    H(U_{Theta-hull}) <= H(U_{q-region})   (+ equal constants).

That is the whole entropy content: a restatement.  No entropy inequality is
thereby produced.

### 4.2 Data processing needs a channel; the channel is the missing object

DPI: if X -> Y is a Markov kernel and Y = f(X) then H(Y) <= H(X).  To apply it
we would need a kernel from the q-pilot distribution to the Theta-hull
distribution.  The only candidate is the multiradial construction algorithm
itself - precisely object (G1).  And if that algorithm existed, the pointwise
monotonicity argument already gives the result; DPI would be a strictly weaker
corollary.  So DPI can never be the route: it presupposes the gap.

### 4.3 Wrong direction, and misapplied

* Entropy power inequality: H(X+Y) >= ... - lower bound for a sum.  Target:
  upper bound for a hull.  Wrong direction.
* Maximum-entropy principle: the uniform distribution *maximizes* entropy for a
  given support; it gives H(U_hull) >= H(any law supported in the hull), again
  a lower bound, useless for bounding the hull from the q side.
* Log-Sobolev / HWI / Talagrand: require a reference Gaussian/log-concave
  measure and a metric-measure space; the carrier is a product of p-adic
  log-shells, with no such structure.
* Union bound (the one *upper*-direction inequality): for P = union_{i<=N} A_i,
  mu_log(phi(P)) <= log N + max_i mu_log(A_i) (after normalization).  This is
  the only information-theoretic statement in the right direction.  It is
  exactly the paper's finiteness/compactness step (10585-10588) and it is *not
  sharp*: it produces |log Theta| <= log N + max_j |log Theta_j|, a different,
  weaker statement, with N uncontrolled (the Ind3 log-Kummer translations are
  indexed by an unbounded lattice; this is exactly why the paper needs the
  WLOG (10530-10534) and the restriction at 10591-10593).

### 4.4 Information geometry has nothing to measure

The one-parameter family of possible images is lam |-> lam*O; in
log-coordinates this is a **location (translation) family**, and
mu_log(lam*O) = mu_log(O) + d*log||lam|| is **affine** in the log coordinate.
Consequently: the Fisher information of this family (where it can be defined at
all) does not depend on lam; there is no curvature and no convexity to exploit;
and the functional carries no information beyond the single scaling exponent.
Moreover a statistical model requires a family of probability distributions
indexed by parameters, whereas the (Ind1)-(Ind3) indeterminacies are *not*
parameters of a model - they are unidentifiability of the arithmetic
holomorphic structure.  Any Fisher metric on the log-shell would be an added
structure incompatible with the paper's O^{triangleright}-monoid data.

**Verdict section 4: REJECT.**  Concrete theorems refused: Shannon/McMillan (no
law), DPI (no channel), EPI (wrong direction), Brascamp-Lieb (needs a Gaussian
reference measure and a geometric Brascamp-Lieb datum), log-Sobolev/Talagrand
(no metric-measure structure), Fisher-Rao/Chentsov (no statistical model).

---

## 5. Brunn-Minkowski and log-concavity

* Classical BM: |A+B|^{1/n} >= |A|^{1/n} + |B|^{1/n}; Prekopa-Leindler:
  int h >= (int f)^{1-t}(int g)^t for h((1-t)x+ty) >= f(x)^{1-t}g(y)^t.  Both
  are **lower** bounds for the volume of a sum.  The target is an **upper**
  bound for the volume of a hull of a union.  Direction mismatch.
* The p-adic/ultrametric analogue is weaker still: for Haar on Q_p^d and
  additive lattices, mu(A+B) >= max(mu(A), mu(B)) - again a lower bound, and in
  the nested-ball case it is an equality (vacuous).
* In the paper the hull is **not a Minkowski sum**: it is the *least* lam*O
  containing the union (Remark 3.9.5(i)), i.e. an infimum in the lattice of
  hulls.  The only "addition" in the carrier is the additive structure of the
  log-shell, where lam*O is a *translate*; Haar is translation invariant, so BM
  degenerates to equality and carries no information.
* Log-concavity/Brascamp-Lieb would require a p-adic analogue of convexity with
  a sharp constant; none exists in the literature, and section 6 shows no such
  uniform statement can hold here.

**Verdict section 5: REJECT** (wrong direction, wrong operation, degenerate in
the actual carrier).

---

## 6. A no-go theorem: no volume-only upper bound on the hull

This is the decisive structural reason all four tool families fail; it also
explains why the paper can only argue by containment.

**Setting.**  X = Q_p^d, d >= 1, additive Haar mu with mu(O) = 1,
mu_log(S) := (1/d)(log mu(S) - log mu(O)) (the Lean
arithmeticTupleNormalizedLogVolume with reference O_canonical), and the hull
operator phi(P) := least lam*O containing P (Remark 3.9.5(i)) for P relatively
compact with finite positive log-volume.

**Proposition.**  For every C in R there is a relatively compact P with
0 < mu(P) < infinity and

    mu_log(phi(P)) > mu_log(P) + C.

**Proof.**  Take d = 1 (the general case is the same computation times d).  For
N >= 1 put P_N := O union (p^{-N} + O).  The two balls are disjoint (since
||p^{-N}|| = p^N > 1), so mu(P_N) = 2 and mu_log(P_N) = log 2.  Any lam*O
containing p^{-N} + O must satisfy ||lam|| >= p^N, and p^{-N}O contains O;
hence phi(P_N) = p^{-N}O, mu(phi(P_N)) = p^N, mu_log(phi(P_N)) = N log p.
Then mu_log(phi(P_N)) - mu_log(P_N) = N log p - log 2 -> infinity.  QED

(The paper's own H_0, H_1, H_P example at 7913-7938 is the N = 1, d = 2 case:
mu_I(P) = 1 < 2 - p^{-1} = mu_I(H_0 union H_1).)

**Corollaries.**

1. There is **no** P-independent inequality
   mu_log(phi(P)) <= mu_log(P) + const; in particular no "hull loses at most a
   bounded amount of volume" principle exists.  Any OT/BM/entropy argument
   would have to be such a principle (they are all uniform in P), so they
   cannot prove the target.
2. The only available upper bound for the hull is the compactness containment
   hull subset lam*O (already the interface's hull_subset_scaleShift), which
   yields a lower bound for the magnitude, i.e. the finiteness statement
   |log Theta| < infinity - *not* |log Theta| <= |log q|.
3. Therefore the target can be proved **only** by a statement about the
   specific Theta-image set, namely that the q-pilot region (or its log-volume)
   is one of the possible output objects.  In Lean this is exactly
   link_implies_inclusion / qPilotNormRegion subset rootNormHull, and in the
   paper it is (IPL)+(SHE)+Fig. 3.8.  This is a *structural* statement; optimal
   transport, entropy, Brunn-Minkowski and information geometry supply no part
   of it.

**Remark (the closest genuine duality, and why it is empty).**  The paper's
sup/inf duality - mu_log(phi(P)) = sup {mu_log(S) | S subset phi(P)} on the
inside and phi(P) = intersection over H superset P of H on the outside - is the
order-theoretic shadow of Kantorovich duality (sup over contents / inf over
containers).  But that duality *is* the monotonicity used in the paper, and it
needs no cost function.  Adding a cost/metric (i.e. passing to genuine OT) only
adds hypotheses.

---

## 6.5 Decision table: each candidate theorem, its hypotheses, the verdict

| # | candidate theorem / tool | standard hypotheses | available here? | verdict | reason | keeps actual q/Theta? |
|---|---|---|---|---|---|---|
| 1 | Kantorovich duality / OT plan | common Polish space, two laws, cost | no space, no law, no cost | REJECT | no coupling; duality yields no mass inequality | no |
| 2 | Brenier / Monge-Ampere | Riemannian structure, regularity, convex cost | no | REJECT | no metric, no regularity on the carrier | no |
| 3 | displacement convexity (McCann) | geodesically convex functional, reference measure | no | REJECT | lower-bound machinery; target is an upper bound | no |
| 4 | Caffarelli contraction | Gaussian reference measures | no | REJECT | no Gaussian structure | no |
| 5 | Birkhoff-von Neumann / HL-P | one common ordered space | no | REJECT | no common order between the theaters | no |
| 6 | data processing inequality | Markov kernel (the multiradial algorithm) | kernel is exactly (G1) | REJECT | presupposes the gap; weaker than monotonicity | no |
| 7 | entropy power inequality | convolution structure | no | REJECT | lower bound for a sum; wrong direction | no |
| 8 | maximum-entropy principle | support constraint only | yes | REJECT (insufficient) | yields H >= ..., a lower bound | partially (uniform Haar) |
| 9 | log-Sobolev / HWI / Talagrand | metric-measure space | no | REJECT | no such structure on p-adic log-shells | no |
| 10 | Fisher-Rao / Chentsov | statistical model with parameters | no | REJECT | indeterminacies are not parameters; family affine in log | no |
| 11 | Brunn-Minkowski / Prekopa-Leindler | convex bodies / measurable sets in R^n | no (wrong operation) | REJECT | lower bounds for sums; the hull is a lattice infimum | no |
| 12 | ultrametric Brunn-Minkowski | lattices in Q_p^d | yes | REJECT | gives mu(A+B) >= max(...), lower bound only | yes, but useless |
| 13 | reverse Brunn-Minkowski (Milman) | Euclidean convex bodies, exponential constant | no | REJECT | no p-adic analogue; section 6 shows it cannot hold | no |
| 14 | union / covering bound | finite union | yes | KEEP (finiteness only) | this is the paper's compactness step; not sharp | yes |
| 15 | closure / adjunction (Remark 3.9.5(ii)) | preorder + monotone valuation + (P1)-(P3) | yes | **KEEP** | this IS the paper's core; already in Lean | yes |
| 16 | Haar scaling law (2l-root) | Haar measure + scaling | yes | **KEEP** | normalization identity for q[2u] | yes |

Rows 14-16 are the whole positive outcome of this exploration; rows 1-13 are
refused, most of them for the structural reason proved in section 6.

---

## 7. What is usable, and what to do next

### 7.1 Keep (paper-faithful, small, already half-present)

**(A) The closure/adjunction package of Remark 3.9.5(ii).**  A HullAdjunction
structure on a preorder with a monotone valuation and (P1)-(P3), deriving
mu_log(P) <= mu_log(phi(P)), phi idempotent, phi(P) = intersection over
H superset P of H, and phi(P) in Phi(P), plus Phi/Xi as in (iii)/(iv).  This is
the paper's abstract Cor 3.12 core, it is real content (it pins down *why* the
inequality is formal), it reuses IQHullLogVolumeInterface, and it can never be
mistaken for a volume estimate.  Consumer: PaperSignedHull /
PaperXiFSourceLink.

**(B) The scaling law for the 2l-root normalization** (the only place where the
q[2u] carrier enters the volumes): mu_log(lam * S) = mu_log(S) + log||lam|| for
lam in Q_p^x (immediate from Haar mu(lam S) = ||lam||^d mu(S) and the 1/d
normalization), hence |log q[2u]| = |log q[1u]|/(2l) and c_root = c_norm/(2l).
This is a *normalization identity*, not an inequality, and it is what makes
rootHalfCoefficient_le_norm (hence the model containment) work.  The root-stack
side (S356) contributes **cardinality bookkeeping only** (2l roots,
l* = (l-1)/2 labels, F_l^x average over l-1 labels, rootSection^(2l) =
qSection).  There is **no** Haar measure and no transport on the root stack in
the source, and none should be invented.

### 7.2 Do not add

Do **not** add any Lean file named/typed after OT, Wasserstein, entropy,
Fisher, Brunn-Minkowski, or "volume comparison".  Every such file would either
(a) restate monotonicity + containment (then it should be stated as such, not
as a transport theorem), or (b) introduce a carrier/measure/coupling that is not
in the source - a surrogate.

### 7.3 Concrete next steps (unchanged target, priority order)

1. **Decompose link_implies_inclusion in the type**, so the structural content
   is visible and no surrogate can fill it:
   (i) qPilotImage subset ThetaHull (carrier-level containment),
   (ii) monotone logVolume (already proved),
   (iii) logVolume qPilotImage = |log q| (q-side normalization).
   Then the target is le_trans and nothing else.  This isolates (G1) as the one
   remaining source obligation.
2. **Prove (A)** as an abstract lemma file (no source hypotheses, no new
   axioms), with Phi/Xi from Remark 3.9.5(iii)(iv).
3. **Prove (B)** for the actual 2l-scaling on the tensor block and connect it to
   rootHalfCoefficient, so the q[2u] normalization is a theorem rather than the
   definitional / (2*l).
4. Keep the S726 no-go as a guard: any future "average of theta magnitudes"
   route is dead by paperHullVsS663ThetaAverageGap_false.
5. **Do not** upgrade the model to a sharp statement: in the model
   |log Theta| = |log q|/(2l) (the label j = +-1 ball is the hull), i.e. the
   model has a factor 2l of slack and the paper's actual hull is much bigger
   (that is what the Ind indeterminacies and the WLOG -|log Theta| < 0 are
   about).  The model inequality is therefore *not* evidence of sharpness.

---

## 8. What would falsify this memo

Any of the following would reopen the route; none is currently available.

* A paper passage using a genuine volume-convexity/isoperimetric estimate (as
  opposed to monotonicity, the hull's minimality, or compactness).  I found none
  in sections 3.9/3.12; the paper explicitly says the *estimates* are IUT IV's
  business (11176-11178) and that the inequality is formal (11081-11084).
* A source-defined probability measure on the possible-image set (not a choice
  of weights).
* A source-defined map (not a poly-isomorphism) between the two theaters, with
  the q-region as its image and a Jacobian sign - that map would *be* (G1).
* A p-adic reverse-Brunn-Minkowski theorem bounding hull volume by the volume
  plus a diameter/spread term, *and* a source bound on that spread.  (Section 6
  shows the diameter term is unavoidable.)

## 9. Status

Research memo.  No Lean statement proved, no file other than this memo written,
no target changed, no fake/surrogate introduced.
statement_compiles: n/a; proof_body_checked: n/a; kernel_closed: n/a;
target_accepted: false.

Cross-reference: the sign lemma and the C9 negative result are in
tmp/sheaf/n8/closure/C9-NEW-OPTIMAL-TRANSPORT-20261025.md (stage-1, no Lean,
target_accepted=false); this memo adds the Cor 3.12 side (down-set membership,
Remark 3.9.5 adjunction, the section 6 no-go) and the decision table.
