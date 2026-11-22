# C1 via LANA eta-reduction: S_q admissibility route

Date: 2026-10-25. Status: C1 OPEN. New reduction, not yet proof. No Lean.

## 0. Goal

C1: exists output D0 (multiradial possible output mod Ind) with logVol(D0)=Q.

LANA formulation (report 9.2):
  R^val, R^ss are pointed one-dimensional real vector spaces;
  eta_q : R^val -> R^ss is the q-pilot native comparison;
  eta^anab_S : R^val -> R^ss is the anabelian/multiradial comparison for
  a subset S of the volume container VC(I_v).
Main goal: exists S with eta_q = eta^anab_S.   (9-1)

## 1. Candidate S_q

Let S_q be the q-pilot region in the volume container: the source's
representation of the q-pilot object at (1,0) on 1,circ U_Q, equivalently
the diagonal {q_v O_v} embedded in VC(I_v) (LANA 9.2: the pilot of the
target R^ss for eta_q is the class of {q_v O_v}).

Write [S] for the class of S in R^ss.

## 2. Lemma A: equality of pointed linear isomorphisms

Lemma A. Let V,W be one-dimensional real vector spaces with distinguished
nonzero pilots p_V, p_W. If f,g : V -> W are linear isomorphisms and
f(p_V)=g(p_V)=p_W, then f=g.

Proof. For any x in V, x=c p_V for some real c (dimension one). Then
f(x)=c f(p_V)=c g(p_V)=g(x). QED.

## 3. Lemma B: pilot classes

By LANA 9.2:
  eta_q(pilot of R^val) = [S_q].          (B1)

For eta^anab_S, the target pilot is by definition the class of M=1·S in R^ss.
Hence for S=S_q:
  eta^anab_{S_q}(pilot of R^val) = [1·S_q] = [S_q].   (B2)

Thus eta_q and eta^anab_{S_q} have the same value at the pilot.

## 4. Conclusion under admissibility

If S_q is admissible for the eta-algorithm (i.e. eta^anab_{S_q} is defined and
is a linear isomorphism of pointed real lines), then Lemma A applies:
  eta_q = eta^anab_{S_q}.                  (4.1)
Then (9-1) holds with S=S_q, hence C1.

Equivalently: C1 reduces to
  (Adm) S_q is an admissible integral structure for the eta-algorithm.

## 5. What is missing

The LANA report says 'once we fix S subset VC(I_v), this provides an
isomorphism eta^anab_S'. This sounds total, but the construction uses 'the
action and S as the integral structure'; arbitrary measurable S need not be
compatible with the N-action/anabelian construction. The exact missing lemma
is:

  (Adm) the q-pilot diagonal S_q is measurable, N-stable, and lies in the
        domain of the anabelian construction of eta^anab.

If (Adm) is a source theorem/definition, C1 follows immediately from Lemmas
A and B. If not, (Adm) is the precise remaining gap, strictly smaller than the
full compatibility (9-1).

## 6. Why this is progress

Previous routes attacked C1 as an existence of a numerical output. This route
separates:
  - linear-map equality (Lemma A): rigorous and elementary;
  - pilot class matching (Lemma B): definitional from LANA 9.2;
  - admissibility of S_q (Adm): the only remaining source condition.

C1 is therefore reduced to (Adm), not restated as an opaque membership.

## 7. Status

C1: OPEN. Reduction to (Adm) proposed. No Lean yet.
Next: audit LANA 9.2/eta construction for the exact domain/admissibility
condition, then prove or refute (Adm).