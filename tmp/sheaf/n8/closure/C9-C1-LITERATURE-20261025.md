# C1 — LITERATURE SEARCH AND INDEPENDENT ATTEMPTS

Date: 2026-10-25. Status: C1 OPEN. No Lean.

C1: exists output D0 (multiradial possible output, mod Ind1/2/3) with
    logVol(D0)=Q=-|log q|.

## 1. Literature findings

### LANA Project Interim Report (July 2026)
URL: https://ncatlab.org/nlab/files/LANAProject-Report-July2026.pdf

The report isolates exactly C1:
  'the relation between the construction arising directly from the q-pilot in
   its native arithmetic holomorphic structure and the construction obtained
   by anabelian and Kummer-theoretic methods through the multiradial procedure.'

It states:
  'At present, however, Project LANA has not yet reconstructed a proof of the
   required compatibility.'

LANA's precise formulation (section 9.2): define
  eta_q : R^val -> R^ss   (q-pilot native construction)
  eta^anab_S : R^val -> R^ss   (anabelian output for a subset S)
The main goal is:
  exists S such that eta_q = eta^anab_S.    (9-1)
This is exactly C1 in LANA's language.

### Minerval claim repository
URL: https://minerval.ai/claims/61843f1b-9b82-4b5f-a4c1-fef4d8aaeb0f

Claim: 'The passage from Theorem 3.11 to Corollary 3.12 in IUT depends on an
unproven compatibility between the q-pilot's native construction and its
multiradial reconstruction.'
Status: supported/verified, credence 0.80; cites LANA, Scholze-Stix, Joshi.

### Kirti Joshi, Arithmetic Teichmuller Spaces III
URL: https://arxiv.org/abs/2401.13508

Joshi claims a proof of Corollary 3.12 by a different route: he defines an
adelic theta-values locus and proves a volume lower bound (Theorem 7.3.1),
then derives the Cor3.12 inequality. His route does not establish the IUT
q-pilot/multiradial compatibility C1; it replaces the IUT comparison by his
arithmetic Teichmuller framework. The special point gives a lower bound, not
an exact output D0 with logVol(D0)=Q.

### Scholze-Stix and critiques
The 2018 Scholze-Stix analysis and later critiques locate the problem at the
same final comparison. Under their simplifying identifications the argument
gives only a trivial inequality. This is evidence that C1 is not proved in the
published IUT argument; it does not supply a proof of C1.

## 2. Independent attempts

A. Choose S = q-pilot diagonal in LANA (9-1).
   The q-pilot diagonal {q_v O_v} lives in the value-group container, not in
   the log-shell volume container VC(I_v); S must be a measurable subset of
   VC(I_v) constructed by the anabelian algorithm. Choosing S from the
   q-pilot is circular unless one proves it is admissible/constructed.

B. Ind-orbit closure: q-pilot appears in the orbit of the algorithmic
   indeterminacy (a question raised at the San Diego bootcamp).
   Ind1/Ind2 preserve normalized log-volume; Ind3 gives only upper-semi
   compatibility. The orbit does not generate the exact value Q, and closure
   would change the target set. No proof.

C. Joshi special point: take D0 = Xi_{z_Theta}, the theta-values lift at the
   special point. Theorem 7.3.1 gives only a lower bound with the l* power
   of q^{1/2l}; the exact log-volume Q is not displayed. Normalization/factor
   mismatch remains. No exact C1.

D. Fixed point: if the anabelian algorithm constructs its q-pilot input, Q is
   a fixed point. There is no map F with F(Q)=Q in the source; APT says not a
   set-theoretic transport. No proof.

E. Solve LANA (9-1) directly: construct S from the q-pilot integral structure
   using SHE. SHE says the construction is expressible under the condition
   that the q-pilot log-volume is Q; it does not produce S. This is the same
   compatibility, restated.

## 3. Conclusion

No independent proof of C1 was found in the literature or constructed here.
LANA explicitly reports the compatibility as unproven. The exact remaining
mathematical problem is LANA (9-1): construct S with eta_q = eta^anab_S, or
prove no such S exists.

C1: OPEN. Cor3.12: conditional on C1. No Lean.