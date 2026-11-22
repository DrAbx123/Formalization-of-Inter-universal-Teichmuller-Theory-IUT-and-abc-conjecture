# C1 domain correction: LANA eta uses VC(I), not VC(LS)

Date: 2026-10-25. Status: C1 OPEN. Source-reading correction.

## 0. Correction

Earlier audits (task-436, 438, 439, 446, 447, 448, 450) assumed
  eta^anab_S domain is S subset VC(LS)  (small/log-shell container).

This is NOT what LANA 9.2 says. Exact LANA text:
  'Once we fix S subset VC(I_v), this provides an isomorphism ...'
  'Rss = {T subset VC(I_v) | adelic and measurable}/~'
  'M = 1*S ... class of M in Rss is the pilot.'
  'pilot of target Rss for eta_q = class of {q_v O_v} embedded diagonally
   into the large volume container VC(I_v).'

So the correct domain is the LARGE container VC(I_v). There is no VC(LS)
object in LANA 9.2. The 'container mismatch' rejection was based on a
misreading and must be retracted.

## 1. What remains true

- S_q = {q_v O_v} is the q-pilot target pilot class in the LARGE container.
- eta^anab_S target pilot is [1*S] = [LGP*S].
- To match eta_q, need [1*S] = [S_q] in Rss.
- The 1 in N acts by LGP multiplication on the LARGE container VC(I_v).

The genuine problem is not container mismatch but:
  (D1) what is the exact domain/image of the LGP action on VC(I_v)?
  (D2) is there an admissible S in VC(I_v) with [1*S]=[S_q]?
  (D3) is eta^anab_S a pointed linear iso?
  (D4) does eta equality give an actual output D0 with logVol(D0)=Q?

## 2. Repaired volume-scaling route

Let T_1 : VC(I) -> VC(I), S |-> 1*S (LGP multiplication).

If T_1 is a measurable map with constant Haar Jacobian J>0 on its domain, and
if admissible S of every positive volume exist in VC(I), choose
  vol(S) = vol(S_q)/J.
Then vol(T_1(S))=vol(S_q), so [T_1(S)]=[S_q].

Then eta^anab_S(pilot)=[1*S]=[S_q]=eta_q(pilot); Lemma A gives eta equality.

Remaining: T_1 domain/image/Jacobian, S admissible, output bridge.

## 3. Alternative exact construction

If LGP is invertible on VC(I) (as an ambient K-vector space) and S=LGP^{-1}S_q
is contained in VC(I) and admissible, then 1*S=S_q exactly, not just by
volume. This is stronger and avoids measure existence. The obstruction is
whether LGP^{-1}S_q lies in the log-shell container and is admissible.

## 4. Consequence for prior audits

The following verdicts are retracted as based on a false domain:
- 'S_q is in large container, eta^anab needs small container': FALSE.
- 'eta^anab_S_q undefined by container mismatch': NOT established.
- 'T_1: VC(LS)->VC(I) undefined': true but irrelevant; the relevant action
  is on VC(I).

The remaining gap is the LGP action/admissibility/output bridge, not a
small/large container mismatch.

## 5. Status

C1: OPEN. Source-reading correction adopted. New subgaps D1-D4.
No Lean yet.