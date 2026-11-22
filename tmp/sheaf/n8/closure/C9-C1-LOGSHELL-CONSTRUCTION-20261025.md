# C1 construction via the log-shell representation of the q-pilot

Date: 2026-10-25. Status: C1 OPEN. New natural-language construction attempt.
No Lean yet.

## 0. Why this is not the S_q route

Previous dead route: take S_q={q_v O_v} in the LARGE container VC(I);
eta^anab_S needs S in the SMALL/log-shell container VC(LS); type mismatch.

This route instead takes the LOG-SHELL REPRESENTATION of the q-pilot,
  S_q^LS := log-Kummer image of the q-pilot value-group data in VC(LS),
which is source-defined by the 1-column representation of the q-pilot on
1,circ U_Q (IUT III Step (xi-d)). Then apply the N/LGP action to move it to
the LARGE container and compare with the q-pilot target pilot.

## 1. Step A: varying Rss

Let VC(I) be the large log-shell volume container with Haar measure mu.
Let M(I) be the adelic measurable subsets T subset VC(I) with
0<mu(T)<infinity.
Define
  Rss := M(I)/~,  T~T' iff mu(T)=mu(T').

Haar measure is non-atomic on the local factors; choose a reference region
O with finite positive volume. The map
  vol : Rss -> R_{>0}, [T] |-> mu(T)/mu(O)
is a bijection, and log vol gives Rss the structure of a one-dimensional real
line. The class [T] is a pilot class; it is nonzero iff T has nonzero volume.

## 2. Step B: Rval and eta_q

Let Rval be the value-group real line C with local pilots phi_v (LANA 4.1(b)).
The q-pilot gives a canonical nonzero pilot p_q in Rval.

The q-pilot diagonal S_q:={q_v O_v} embedded in VC(I) has a class [S_q] in
Rss and nonzero finite volume V_q=mu(S_q)/mu(O)>0.
Define the linear map
  eta_q : Rval -> Rss,  p_q |-> [S_q],
extended by R-linearity. It is a pointed linear isomorphism because both
sides are one-dimensional and p_q,[S_q] are nonzero.

## 3. Step C: the log-shell q-pilot region S_q^LS

By IUT III Step (xi-d), the q-pilot object at (1,0) is represented on
1,circ U_Q via the 1-column log-Kummer correspondence; the region that arises
from this representation has log-volume -|log q|=Q. Let
  S_q^LS subset VC(LS)
be this log-shell region: the image of the q-pilot value-group data under the
log-Kummer correspondence (equivalently, the log of the q-pilot fractional
ideal data in the log-shell container).

S_q^LS is source-defined, adelic measurable, and has finite positive volume;
its class is the small-container representative of the q-pilot.

## 4. Step D: N/LGP action and target class

Let 1 in N act by LGP on the large volume container:
  T_1 : VC(I) -> VC(I),  U |-> LGP·U.
This is the source action of the Gaussian monoid on log-shells (Figure 3.1;
Theorem3.11); it is a measurable bijection with constant Haar scaling.

Key construction claim:
  T_1(S_q^LS) has the same class in Rss as S_q.       (D)
Equivalently, the LGP translate of the log-shell q-pilot region is the
q-pilot diagonal region in the large container. This is the compatibility of
the log-Kummer representation with the LGP action, i.e. the q-pilot side of
SHE/xi-e.

## 5. Step E: eta^anab_{S_q^LS}

By LANA 9.2, for S=S_q^LS in VC(LS), the anabelian construction gives
  eta^anab_{S_q^LS} : Rval -> Rss,
with target pilot
  eta^anab_{S_q^LS}(p_q) = [M],  M=1·S_q^LS = T_1(S_q^LS).
By (D), [M]=[S_q]. Hence
  eta^anab_{S_q^LS}(p_q) = [S_q] = eta_q(p_q).

S_q^LS is admissible because it is the source log-Kummer representation of
the q-pilot, and the anabelian N-action is defined on it by Theorem3.11.

## 6. Step F: eta equality and C1

Lemma A (pointed one-dimensional linear isomorphisms agreeing at a nonzero
pilot): eta_q = eta^anab_{S_q^LS}.

This is LANA (9-1). To obtain C1, use the source's xi-e/f: the multiradial
construction of output possibilities constitutes a construction of the input
q-pilot log-volume; hence there is an output D0 in O with logVol(D0)=Q.
Equivalently, the eta equality identifies the q-pilot pilot with a possible
output log-volume; this is the output bridge.

Thus C1.

## 7. Exact gaps

G1. Existence and properties of S_q^LS: log-Kummer image of q-pilot in
    VC(LS), measurable, finite positive volume, adelic.
G2. The key class equality (D): T_1(S_q^LS) has class [S_q] in Rss.
G3. Admissibility of S_q^LS for eta^anab (integral/N-compatible).
G4. eta^anab_{S_q^LS} is a pointed linear isomorphism.
G5. The eta equality -> output D0 bridge (xi-e/f).

G1/G2 are the new content; G3/G4 are LANA's suitable-S conditions; G5 is
the output bridge. This route is different from S_q and volume-scaling:
the S is the log-shell q-pilot region, not q_vO_v itself.

## 8. Status

C1: OPEN. Construction proposed; gaps G1-G5 to be checked. No Lean yet.