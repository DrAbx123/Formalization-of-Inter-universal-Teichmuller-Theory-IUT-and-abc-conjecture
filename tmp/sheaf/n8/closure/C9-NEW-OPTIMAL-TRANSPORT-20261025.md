# C9 new program: optimal transport of q-pilot vs hull measures

Task: task-244 (Creative new-math program: optimal transport of q-pilot vs
hull measures). Owner: volumedet. Date: 2026-10-25. Stage1 natural-language/
hypothesis/theorem-attempt only. No arbitrary measures, no Lean/Project/target
edits. Only this file written. `target_accepted=false`.

Inputs: C9 q-pilot/BPS/Theta assembly, C9-GLOBAL-ASSEMBLY-CORRECTED2,
C9-ARCH-NORMALIZATION-CORRECTION, C9-MASTER-CONTRADICTION, C9-NEGATIVE-GLOBAL,
C9-MOD41-EXACT-G-20261025.md, C9-EJ-COMPLETION. The actual complete C, target
hull H_C, q-pilot measure and BPS data remain conditional/missing; this file
does not assume them.

## 0. Verdict

A natural volume-nonincreasing transport from the q-pilot measure mu_Q to the
target hull measure mu_H proves the **opposite** inequality from P6:

    T_* mu_Q = mu_H,  T volume-nonincreasing
      =>  h_C <= Q_C,   not Q_C <= h_C.                       (0.1)

To prove `Q_C <= h_C` one needs either

    (a) a volume-nonincreasing transport mu_H -> mu_Q (a retraction of the
        q-pilot to the hull), or
    (b) a volume-**nondecreasing/expanding** transport mu_Q -> mu_H.

Neither is supplied by the C9/BPS/Theta data. The natural possible-image map
goes q-pilot -> hull; holomorphic/psh hull formation is volume-contracting, so
the natural direction gives (0.1), i.e. a conditional counterexample direction,
not the P6 target. A reverse transport/expansion is an extra structure
equivalent to the missing target-containment/naturality input (not H_A/B,
but TC-C-type).

For the b=3 E_j profile: `D_3=93.714971...`, `A=13.164394...`, and
`D_3-A=80.550578...>0`. A contraction naturally explains a **hull deficit**
of that size; it cannot account for an expansion sufficient to close P6.
Thus the transport/compression program cannot prove P6 in its natural
orientation, and it does not provide a branch-independent contradiction.

## 1. Measures and sign conventions

Let `X_Q` be the actual q-pilot object/region and `H_C` the complete final
target holomorphic hull. The normalized log-volumes are

    Q_C = log M_Q,   h_C = log M_H,                         (1.1)

where `M_Q,M_H>0` are the normalized total masses. The target P6 is

    h_C >= Q_C   <=>   M_H >= M_Q.                           (1.2)

Canonical source measures, if constructed, would be the normalized
Haar/log-volume measures on the q-pilot and on H_C; their total masses are
fixed by Q_C,h_C. No arbitrary measure is introduced. In the current corpus
the actual q-pilot measure and H_C are missing, so all transport statements
below are conditional on the source/BPS/TC data.

Because log-volume is monotone under inclusion and additive under disjoint
union, a pushforward by a volume-nonincreasing map satisfies

    logvol(T_* mu) <= logvol(mu).                            (1.3)

This sign is the entire obstruction.

## 2. Transport lemma and its orientation

### Lemma 2.1 (contraction goes the wrong way)

Let `T:X_Q -> H_C` be measurable with `T_*mu_Q=mu_H`. If T is
volume-nonincreasing (Jacobian log <=0 on the support, equivalently
`logvol(T(E)) <= logvol(E)` for all relevant E), then

    h_C = logvol(mu_H) = logvol(T_*mu_Q) <= logvol(mu_Q)=Q_C. (2.1)

Thus a natural contraction proves `h_C<=Q_C`, the negation-side of P6, not
P6. If T is strictly contracting on a set of positive measure, the inequality
is strict and gives a conditional counterexample direction `h_C<Q_C`
(provided the target-container conditions make h_C the actual target
volume).

### Lemma 2.2 (what would prove P6)

P6 follows from either of:

(i) a volume-nonincreasing transport `S:H_C -> X_Q` with `S_*mu_H=mu_Q`;
then `Q_C=logvol(S_*mu_H)<=h_C`;

(ii) a volume-nondecreasing/expanding transport `T:X_Q -> H_C` with
`T_*mu_Q=mu_H`; then `h_C>=Q_C`.

Both require a **reversal/expansion** not present in the q-pilot possible-image
construction. The natural Θ-pilot map is q-pilot -> hull; no natural map
hull -> q-pilot is supplied. A section/retraction would be an extra choice
(and would be arbitrary unless source-defined).

### Lemma 2.3 (Monge-Kantorovich form)

For any cost `c` and transport plan pi between mu_Q and mu_H, the
Kantorovich duality gives costs/distances, not a free volume inequality.
A contraction estimate of the form `W_1(mu_Q,mu_H) <= C` does not imply
`M_H>=M_Q`; it only controls displacement. To derive mass comparison one
must separately know the Jacobian/volume orientation. Thus optimal transport
does not by itself fix the sign.

## 3. Natural maps in the C9 data

### 3.1 q-pilot -> hull (natural, contracting)

The Θ-pilot possible image `T_Θ(A(S))` is a map from the source q-pilot
object to the target hull region. Holomorphic hull formation is a closure
operation: the hull can be larger than a particular image but the normalized
measure comparison is not automatic; the actual TC-C condition is exactly
the missing statement that the target normalized volume is preserved or
tracked. In the natural orientation, even a measure-preserving image would
give h_C=Q_C, not h_C>=Q_C; a contraction gives h_C<Q_C.

### 3.2 hull -> q-pilot (not natural)

To apply Lemma 2.2(i) one needs a retraction/section from the hull back to
the q-pilot, or an inverse measure transport. The source gives the q-pilot as
a domain and the hull as a possible image; it does not give a canonical
inverse. Choosing one is an arbitrary construction and is not allowed.

### 3.3 B=O_K/B=I does not repair the orientation

The transport program was proposed as avoiding H_A/B. It indeed does not use
the B-branch. But it replaces it by a map/measure comparison that is at least
as strong as TC-C: it must identify the actual q-pilot and hull measures and
their pushforward. H_A/B is not the only missing input; the q-pilot measure,
BPS/Theta normalization and target H_C are missing independently. A transport
map with the needed expansion is an extra source structure, not a consequence
of q-pilot possible images.

## 4. Monge-Ampere / plurisubharmonic comparison

Let `phi` be a psh weight on a target neighborhood with
`MA(phi)=mu_H` and `mu_Q` a reference measure. The comparison principle
typically gives

    mu_H <= mu_Q  (or MA(phi)<=MA(psi))  =>  volumes compare h_C<=Q_C,

again the wrong direction for P6. A reverse comparison `mu_Q<=mu_H` or a
plurisubharmonic domination `phi>=psi` with the correct mass orientation
would be needed; no source theorem supplies it. Complex-geometric maps and
hull formation are volume-contracting in the natural direction, so the
Monge-Ampere route has the same sign obstruction as Lemma 2.1.

A possible **new-math hypothesis** is:

    (OT-exp) there is a canonical transport q-pilot -> hull with
    log-Jacobian >=0 and total mass M_H>=M_Q, derived from the
    Θ-pilot/BPS data without choosing a branch.

Under (OT-exp), P6 follows immediately from Lemma 2.2(ii). But (OT-exp) is
not a theorem or construction in the corpus; it is a hypothesis equivalent to
a strong expansion/containment statement. It cannot be assumed as a
source fact, and it is not implied by the natural q-pilot possible-image map.

## 5. Test on the b=3 E_j profile

The uniform b=3 local data (conditional finite donor, p=12301, e=41) give

    Q_p=-3/41 log p,  h_A=-411/41 log p,  D_3=Q_p-h_A=408/41 log p,
    D_3=93.71497127459669...,
    A=13.164393687268102... .                            (5.1)

At the level of masses, the local hull/q-pilot ratio (if the local profiles
were actual target volumes) is `e^{-D_3}` before archimedean compensation.
Even the paper-level archimedean bound contributes at most `e^{A}`, leaving
a contraction/expansion gap of `e^{D_3-A}=e^{80.550577...}`. The transport
program would need an **expansion** by this enormous factor or a reverse
volume-nonincreasing map. The natural q-pilot -> hull map is contracting, so
it accounts for the deficit in the **opposite** direction: it is consistent
with `h_C<Q_C`, not with `h_C>=Q_C`.

Thus on b=3 the program does not close the gap; it exhibits the compression
gap. A strict contraction would be a conditional counterexample direction
(if target containment/TC-C and the actual q-pilot/hull measures were
constructed), not a proof of P6.

## 6. Branch-independent contradiction attempt

Transport is branch-independent only in the sense that it does not mention
B=O_K/B=I. That does not make it a contradiction:

- If the only natural transport is contracting q-pilot -> hull, the resulting
  inequality is `h_C<=Q_C`, which is the **wrong side** of P6; it supports a
  deficit/counterexample, not closure.
- To obtain `Q_C<=h_C` one must reverse or expand; the reverse map is
  arbitrary/missing, and the expansion hypothesis is not source-derived.
- The b=3 numbers show the needed expansion is at least `e^{80.55}` beyond
  the archimedean upper bound; no good finite/tensor/Ind1-3/other-local
  contribution supplies it (see C9-NEGATIVE-GLOBAL).

Therefore the transport route does not give a branch-independent
contradiction. A branch-independent **counterexample** direction would need
an actual q-pilot->hull contraction plus target containment; that is also
missing and would not prove P6.

## 7. Actual / conditional / impossible / open

PROVED (elementary sign lemma):

- A volume-nonincreasing pushforward q-pilot -> hull implies
  `h_C<=Q_C`; a volume-nonincreasing pushforward hull -> q-pilot or a
  volume-nondecreasing q-pilot -> hull implies `Q_C<=h_C`.
- Optimal transport/Kantorovich duality and Monge-Ampere comparison do not
  by themselves supply the needed orientation; the sign must be checked.

CONDITIONAL:

- Existence of actual q-pilot/hull normalized measures and a canonical
  Θ-pilot pushforward; TC-C identifies h_C with the target hull volume.
- The b=3 D_3/A values (conditional finite donor; arch normalization).
- The OT-exp hypothesis would imply P6, but it is a new hypothesis.

IMPOSSIBLE as a source construction:

- obtaining `Q_C<=h_C` from a natural contraction q-pilot -> hull;
- using Monge-Ampere/psh comparison in the contracting direction as a P6
  proof;
- treating a reverse map/expansion as automatic or branch-independent;
- using arbitrary measures/weights to force the sign.

OPEN/MISSING:

- actual complete C, q-pilot measure, BPS/Theta measure, target hull H_C;
- canonical transport/retraction or expansion theorem;
- TC-A..H/TC-S; actual archimedean/other-local data; fixed q class;
- any global P6 proof or counterexample.

## 8. Conclusion

The natural transport direction is q-pilot -> hull, and natural
holomorphic/hull maps are volume-contracting. That yields
`h_C<=Q_C`, the opposite of P6. To prove `Q_C<=h_C` one needs a reverse
volume-nonincreasing transport or an expansion; neither is supplied by the
C9/BPS/Theta data, and postulating it is a new hypothesis (OT-exp)
equivalent to the missing containment/volume comparison. On b=3, the
contraction/expansion gap is at least `e^{80.55}`, far beyond the Archimedean
upper bound, so compression accounts for the deficit but cannot close it.
The transport program is therefore a precise **negative** result for the
current route, not a P6 proof.

## 9. Status

Stage1 natural-language new-math exploration only. No arbitrary measure,
no Lean/Project edits. Only this file written. `target_accepted=false`;
complete C9/P6 not proved.
