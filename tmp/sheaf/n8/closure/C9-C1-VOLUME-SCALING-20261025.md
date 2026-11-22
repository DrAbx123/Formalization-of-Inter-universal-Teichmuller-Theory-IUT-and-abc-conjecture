# C1 via volume-scaling of the N-action (new route)

Date: 2026-10-25. Status: C1 OPEN. New candidate, not yet proof. No Lean.

## 0. Idea

Previous S_q route failed because S_q is a pilot class in the LARGE container,
not an admissible S in the small/log-shell container VC(LS).

Instead of taking S=S_q, choose a region S in VC(LS) whose N-translate T(S)
has the same volume class as S_q. Then
  eta^anab_S pilot = [T(S)] = [S_q] = eta_q pilot,
so the two pointed linear isomorphisms agree and eta_q=eta^anab_S.

## 1. Setup

VC(LS): small/log-shell volume container.
VC(I): large/target volume container.
Rss = {T subset VC(I) | T adelic measurable}/~, T~T' iff same volume.

q-pilot target pilot: S_q in VC(I), volume V_q>0, Q=log V_q.

N-action: 1 in N acts by LGP; denote the induced map
  T_1 : VC(LS) -> VC(I),  S |-> 1·S.

Assume (H1) T_1 is a measurable bijection onto its image with constant
Jacobian J>0: vol(T_1(S))=J*vol(S) for every measurable S.

## 2. Volume existence

Lemma B. If VC(LS) has measurable subsets of every volume in (0,vol_total),
then for V_q/J there exists a measurable S subset VC(LS) with vol(S)=V_q/J.

Proof. The measure is non-atomic on the log-shell container; standard
intermediate-value theorem for non-atomic finite measures. QED.

Then vol(T_1(S))=J*(V_q/J)=V_q, hence [T_1(S)]=[S_q] in Rss.

## 3. Eta pilot equality

LANA 9.2:
  eta_q pilot = [S_q];
  eta^anab_S pilot = [1·S] = [T_1(S)].

By Lemma B, [T_1(S)]=[S_q]. Hence
  eta_q(pilot)=eta^anab_S(pilot).

Lemma A (pointed one-dimensional linear isomorphisms agreeing at a nonzero
pilot): eta_q=eta^anab_S.

## 4. C1

If eta_q=eta^anab_S, LANA (9-1) holds. Then the q-pilot value is realized by
the anabelian construction; to obtain C1 as output membership one still needs
the bridge:
  (Bridge) eta equality -> exists output D0 in O with logVol(D0)=Q.

The volume-scaling route proves the eta equality part under H1/Lemma B and
reduces C1 to (Bridge).

## 5. Exact gaps

G1. T_1 is a measurable bijection with constant Jacobian J (actual LGP action).
G2. VC(LS) has measurable subsets of every volume (non-atomic, finite).
G3. The chosen S is admissible/integral for eta^anab (not just measurable).
G4. S_q volume V_q and [T_1(S)]=[S_q] in the correct Rss quotient.
G5. Bridge eta equality -> actual output D0 with logVol(D0)=Q.

G1/G2 are measure-theoretic and may be provable from Haar/volume container;
G3/G5 are the remaining source/bridge content.

## 6. Why this is different from S_q

S_q route: S=S_q in LARGE container; eta^anab undefined (container mismatch).
Scaling route: S is a region in SMALL container, chosen by volume; T_1(S) is
the target pilot class in LARGE container. It respects the LANA domain.

## 7. Status

C1: OPEN. New volume-scaling route proposed. No Lean yet.