# C9 C1 volume measure: Lemma B measure existence

Task: task-442. Owner: multiradial. Date: 2026-10-25.
Rigorous natural-language measure-theoretic proof/refutation only. No Lean/Project
edits; no mixed/E3; no arbitrary data. Deliverable: this file only.
target_accepted=false; C1/P6 open.

## 0. Lemma B and exact claim

Lemma B (measure-existence form):

    Let VC(LS) be the log-shell version of the volume container, with its
    Haar measure normalized as in LANA §5.2(e). Then VC(LS) has measurable
    subsets of every volume in (0,total), where total = vol(VC(LS)) is finite
    and positive; equivalently the measure is non-atomic and finite.

This is the measure-existence lemma used to choose an S_q of prescribed
q-pilot volume. It is NOT the eta target-pilot equality
[S_q]=[1·S_q]; that is a separate N/LGP-invariance condition (task-437).

Verdict: ACCEPTED for the exact compact log-shell space VC(I) with its
normalized Haar measure. The proof is below. Caveats:
  - if VC(LS) is taken to be the rationalized container VC(I)⊗_Z Q, the total
    Haar measure is not finite and Lemma B is not applicable (total infinite;
    no finite non-atomic probability space);
  - if VC(LS) is taken to be the K-version VC(K) with archimedean factors K_v
    (noncompact R/C), the total measure is infinite; Lemma B is false as a
    finite-measure statement;
  - if the measure is a discrete/counting measure with atoms, the range need
    not be all (0,total).
The exact source space is the log-shell version, so the accepted form is
VC(I), not VC(K) or VC(I)⊗Q.

## 1. Exact source definitions

LANA §5.2 (extracted text lines 1565-1628):

  - Small volume container: direct product ∏_{v∈V} K_v.
  - Large local volume container over v:
        LocVC(K)_v = ⊕_{j∈J} K_{S_{j+1},v},
    J = F_l^×/{±1} = {0,1,...,l*}, S_j = {0,...,j-1}; finite direct sum of
    finite tensor products.
  - Large volume container:
        VC(K) = ∏_{v∈V} LocVC(K)_v.
  - Log-shell version: replace K_v by the log-shell I_v and ⊗_{Q_v}Q by
    ⊗_{Z_v}Q:
        LocVC(I)_v = ⊕_{j∈J} I_{S_{j+1},v},
        VC(I) = ∏_{v∈V} LocVC(I)_v.
  - O-version VC(O) replaces K_v by O_v; volume normalization:
        vol(VC(O)) = 1,
        multiplication by p_v at v multiplies volume by p_v^{-1};
        log-vol(S) = log vol(S).
  - The procession normalization is this Haar measure normalization
    (Remark5.2.1).

The possible images are stated as LGP·U ⊆ VC(I)⊗_Z Q (line 2088), but the
R^ss volume classes use measurable subsets S ⊂ VC(I_v) (lines 2567-2573), not
the rationalization. The measure-existence statement is about VC(I_v)/VC(I).

## 2. VC(I) is a compact metrizable abelian group with finite Haar measure

Let V be finite (initial Theta-data; LANA §2). For each v and each tensor
factor in LocVC(I)_v:

  - I_v is a compact Z_p-module (log-shell; LANA §5.1: I_v is the image of the
    compact unit group O_v^× under log, scaled by (2p_v)^{-1}; it is the
    compact integral structure used in the volume container). The same
    compactness is used for the four log-shell variants in §5.1(a)-(d).
  - A finite tensor product and finite direct sum of compact Z_p-modules is a
    compact Z_p-module.
  - The product over the finite set V of compact local containers is compact.

Thus VC(I) is a compact (hence locally compact) metrizable abelian topological
group. Its Haar measure is finite: finite product of finite Haar measures of
the compact local factors. Since I_v contains O_v (LANA: the factor (2p_v)^{-1}
makes O_v ⊂ I_v), VC(I) contains VC(O), so

    0 < vol(VC(O)) = 1 <= vol(VC(I)) =: T < infinity.             (2.1)

The exact finite value T is not needed for Lemma B; only 0<T<infinity is used.
The normalization is the LANA one (vol(VC(O))=1, p_v multiplier p_v^{-1});
changing the normalization rescales T but not the range statement.

## 3. VC(I) has no atoms

Claim 3.1. The normalized Haar measure m on VC(I) is non-atomic: every
singleton has measure zero, and more generally there is no measurable atom of
positive measure.

Proof. It suffices to consider the local log-shell I_v. I_v is an infinite
compact Z_p-module (at nonarchimedean v it contains the infinite descending
chain p^n I_v; at archimedean v it is an infinite compact real torus/ball
factor). Suppose a point x in I_v had m_v({x})=c>0. By translation invariance
of Haar measure, all points have measure c. Since I_v is infinite and m_v is
finite, this is impossible: an infinite sum of c over distinct points would
exceed m_v(I_v). Hence m_v({x})=0 for every point. More generally, if a
measurable atom A had m_v(A)>0, then by regularity/translation invariance and
the standard Haar-measure theorem on non-discrete compact groups, all the
translated atoms would have the same positive measure; a finite measure space
can have only finitely many disjoint positive-measure translates, forcing the
group to be a finite union of atoms, hence finite — contradiction with the
infinite log-shell. Therefore m_v is non-atomic. A finite product of
non-atomic finite measures is non-atomic: if A has positive measure in the
product, one of its fibers has positive measure, and a non-atomic factor
splits it. Hence m on VC(I) is non-atomic. QED.

The key point is that log-shells are infinite compact p-adic/archimedean
objects, not finite sets. If one replaced I_v by a finite quotient or used a
counting measure, atoms could appear; that is excluded by the exact space.

## 4. Non-atomic finite measure range theorem

We use the standard measure-theoretic fact:

Theorem 4.1 (non-atomic finite measure range). Let (X,Σ,m) be a finite
measure space with m(X)=T and with no atoms. Then for every t in [0,T] there
exists a measurable subset E⊂X with m(E)=t. In particular, for every
t in (0,T), measurable subsets of volume exactly t exist.

Proof sketch (standard; included for rigor).
  (i) Non-atomicity implies the splitting lemma: for every measurable A with
      m(A)>0 and every s with 0<s<m(A), there is a measurable B⊂A with
      m(B)=s. Indeed, if no such B existed, the measure algebra would have an
      atom inside A; a non-atomic finite measure algebra has no such gap.
      A standard way to see the splitting is to use the measurable-isomorphism
      theorem: a finite non-atomic measure on a standard Borel space is
      isomorphic to Lebesgue measure on [0,T], where the interval subsets of
      every measure are immediate. VC(I) is compact metrizable, hence standard
      Borel, so the theorem applies.
  (ii) Alternatively, by repeated splitting into halves one constructs, for
      every dyadic rational q in [0,T], a measurable set of measure q. For
      general t, take a binary expansion t/T=0.b1b2... and choose nested
      dyadic sets A_n⊂A_{n+1} with m(A_n)=sum_{k<=n} b_k T/2^k. The union
      A=∪A_n is measurable and m(A)=sum b_k T/2^k=t by continuity from below
      (finite measure).
  (iii) Endpoints: empty set for 0, X for T.
This proves the range statement. QED.

For VC(I), T=vol(VC(I)) is finite positive by (2.1), and m is non-atomic by
Claim 3.1. Therefore:

    for every t in (0,T), there exists a measurable S⊂VC(I) with vol(S)=t. (4.1)

This is Lemma B measure existence, for the exact compact log-shell space.

## 5. Application to q-pilot volume

The q-pilot log-volume is Q=-|log q|<0 because |log q|>0. Its positive volume
is

    vol_q := exp(Q) = exp(-|log q|) in (0,1).                       (5.1)

Since T=vol(VC(I))>=1 (VC(I) contains VC(O), volume 1), vol_q in (0,1) is in
(0,T). By (4.1), there exists a measurable S_q⊂VC(I) with

    vol(S_q) = vol_q,   log-vol(S_q) = Q.                           (5.2)

Thus the measure-existence part needed for choosing an S_q of q-pilot volume
is available. This is the positive content of Lemma B.

Important limitation: (5.2) does not assert

    vol(1·S_q) = vol(S_q),   i.e. [S_q]=[1·S_q] in R^ss.             (5.3)

The action of 1 in N is the LGP action, not the identity; it may change the
volume. Lemma B measure existence gives a subset of prescribed volume but not
an N-invariant subset. The eta target-pilot equality (5.3) remains the separate
task-437 gap (E-eta). Measure existence alone does not prove eta_q=eta^anab or
C1.

## 6. Refutation of false variants

The following variants are false/not applicable:

  (V1) VC(LS)=VC(K) with archimedean factors K_v=R or C: Haar measure of R/C is
       infinite; total T=infinity; no finite non-atomic probability space. The
       range statement "every volume in (0,total)" has total infinity and the
       intended finite-measure lemma fails.
  (V2) VC(LS)=VC(I)⊗_Z Q: the rationalization is not compact and does not
       carry the finite Haar measure normalized by vol(VC(O))=1; total is
       infinite/undefined. Lemma B is not applicable.
  (V3) A finite/discrete quotient or counting measure: atoms appear; the range
       is a discrete set of integers, not all volumes. Non-atomicity is
       essential.
  (V4) A non-normalized Haar measure with infinite total: no finite total T;
       the statement "every volume in (0,total)" is vacuous/not the intended
       finite-measure lemma.

The exact LANA space is VC(I) (log-shell version), compact with finite Haar
measure; (V1)-(V4) are excluded by the source definition.

## 7. Verdict

ACCEPT Lemma B in the exact form:

    VC(I) (log-shell volume container) with the LANA normalized Haar measure
    is a compact metrizable abelian group of finite positive total measure T;
    it is non-atomic; hence for every volume in (0,T) there is a measurable
    subset of that volume. In particular, a measurable S_q of q-pilot volume
    exp(Q) exists.

REJECT the lemma for VC(K), VC(I)⊗_Z Q, finite/discrete quotients, counting
measures, or unnormalized infinite Haar measures. Those variants either have
infinite total, atoms, or no finite normalization.

Caveat for C1: Lemma B measure existence is necessary for choosing S_q but is
NOT sufficient for the eta target-pilot equality [S_q]=[1·S_q] or for C1.
The N/LGP action on S_q and the exact q-pilot diagonal class must still be
verified; otherwise eta_q and eta^anab_{S_q} can have different target pilots.
No Lean/Project edits; no mixed/E3; no arbitrary S_q beyond the measurable
existence theorem. target_accepted=false; C1/P6 open.

## 8. Acceptance

Only C9-C1-VOL-MEASURE-20261025.md written. Natural-language measure-theoretic
proof/refutation only; no Lean/Project/target edits; no independent review/
kernel/comparator run. target_accepted=false; C1/P6 open.
