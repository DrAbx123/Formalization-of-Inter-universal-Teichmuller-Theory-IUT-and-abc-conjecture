# C9 C1 domain audit: verify the "corrected" LANA eta domain

Task: task-451. Date: 2026-10-25. Author: transport.
Audit of C9-C1-DOMAIN-CORRECTION-20261025.md against LANA 9.2.
No Lean; no mixed/E3; no arbitrary. Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-C1-DOMAIN-CORRECTION-20261025.md | 68 | D10554BCFC0617DEA21F8D3860DC217FC53C3952AC08AA4F4E075A461976EFA5 |
| C9-STRICT-DEFICIT-LANA-SNAPSHOT-20261024.tex | 2726 | 3E613BEE63EFBFA7B17178566DD837D1CD92ED21491EC6E65D534B3521FC58BF |

Relevant LANA lines: 2502-2523 (section 9.2, "The main goal").

## 1. Verdict

The "correction" is WRONG. LANA 9.2 does NOT say that the eta^anab_S domain is
S subset VC(I_v). The exact source says:

    Once we fix S subset VC(LS_uv), this provides an isomorphism ...

and only for the TARGET does it use the large container:

    R^ss = {T subset VC(I_uv) | adelic and measurable} / ~.

The correction conflates the domain container VC(LS_uv) with the target
container VC(I_uv). The prior container-mismatch verdicts are correct and must
NOT be retracted.

Therefore:

- The corrected domain VC(I) is REJECTED.
- The exact domain remains VC(LS_uv): S is a subset of the log-shell/small
  volume container, while the target class [1.S] lies in R^ss built from
  adelic measurable subsets of the large container VC(I_uv).
- S_q={q_v O_v} is the q-pilot target pilot class in the large container, not
  an admissible S for eta^anab_S.
- The C1 eta-reduction and the log-shell construction remain rejected at the
  domain level.

## 2. Exact LANA 9.2 quotes

LANA snapshot, lines 2502-2517:

Line 2506:

    Once we fix S subset VC(LS_uv), this provides an isomorphism between the
    C part of the original BPS (denoted R^val) and the C constructed using the
    action and S as the integral structure, denoted R^ss; more precisely,

Line 2508:

    R^ss = {T subset VC(I_uv) | adelic and measurable} / ~,

where T ~ T' if and only if the volume of T coincides with that of T'.

Line 2510:

    we define M=1.S (the action of 1 in N), which represents "LGP.S", and put
    the class of M in R^ss to be the pilot.

Lines 2511-2513:

    Thus the isomorphism eta^anab_S : R^val ~> R^ss of the pointed real vector
    spaces depends on S, and is constructed via anabelian methods as discussed
    above.

Lines 2515-2517:

    On the other hand, when we work with a BPS that was constructed as the
    q-BPS of a Hodge theater, this perspective provides us with an isomorphism
    eta^q : R^val ~> R^ss, where the pilot of the target R^ss is given by the
    class of {q_v O_v} embedded "diagonally" into the large volume container
    VC(I_uv).

Key distinction:

- domain variable: S in VC(LS_uv);
- target: R^ss from adelic measurable T in VC(I_uv);
- q-pilot target pilot: class of {q_vO_v} in the LARGE container VC(I_uv).

## 3. Audit of the correction's claims

### Claim in section 0: "Earlier audits assumed eta^anab_S domain is S subset VC(LS). This is NOT what LANA 9.2 says."

REJECT. This is exactly what LANA 9.2 says at line 2506:
S subset VC(LS_uv). The correction misquotes the source.

### Claim in section 0: "Exact LANA text: 'Once we fix S subset VC(I_v)...'"

REJECT. The exact source line is S subset VC(LS_uv), not VC(I_v).
The correction substitutes the target container for the domain container.

### Claim in section 0: "There is no VC(LS) object in LANA 9.2."

REJECT. VC(LS_uv) occurs in the exact line 2506. What is true is that the
TARGET R^ss uses VC(I_uv), and the q-pilot target uses the large container.
Both containers occur in 9.2, in different roles.

### Claim in section 0: "The container-mismatch rejection was based on a misreading and must be retracted."

REJECT. Prior verdicts (task-436, 441, 446) correctly distinguish:
- eta^anab_S domain: S subset VC(LS_uv);
- eta_q target pilot: {q_vO_v} in VC(I_uv).
The mismatch is real: S_q is a target object in the large container, not an
admissible S in the small/log-shell container.

### Claim in section 1: "What remains true"

PARTIALLY TRUE, but mislabeled:

- S_q={q_vO_v} is the q-pilot target pilot class in the large container. TRUE.
- eta^anab_S target pilot is [1.S]=[LGP.S]. TRUE as LANA line 2510.
- To match eta_q, need [1.S]=[S_q] in R^ss. TRUE.
- The 1 in N acts by LGP multiplication on the large container VC(I_v). TRUE
  for the source action; but S is not allowed to be an arbitrary large-container
  subset in eta^anab_S.
- "The correct domain is the large container VC(I_v)" FALSE.

### Claim in section 2: "Repaired volume-scaling route T_1:VC(I)->VC(I)"

REJECT as a repair. T_1 on VC(I) is the source LGP action, but an S chosen in
VC(I) is not in the eta^anab_S domain VC(LS_uv). The route replaces the domain
condition by the target container; this is exactly the container mismatch.

### Claim in section 3: "Alternative S=LGP^{-1}S_q in VC(I), admissible"

REJECT. S=LGP^{-1}S_q lies in the large container VC(I), not in the eta domain
VC(LS_uv). It is not admissible for eta^anab_S. The exact equality
1.S=S_q is irrelevant if S is outside the domain.

### Claim in section 4: retraction list

REJECT all three retractions:

1. "S_q is in large container, eta^anab needs small container: FALSE" —
   the statement is TRUE; source line 2506.
2. "eta^anab_{S_q} undefined by container mismatch: NOT established" —
   it IS undefined by the source domain; S_q is not a subset of VC(LS_uv).
3. "T_1:VC(LS)->VC(I) undefined: true but irrelevant" — the claim that
   T_1:VC(LS)->VC(I) is undefined remains true; the relevant eta domain is
   small, so the irrelevance claim is wrong.

## 4. Exact answer to the task question

Question: is the corrected LANA eta domain VC(I_v), or VC(LS)?

Answer: VC(LS_uv). LANA 9.2 line 2506 says S subset VC(LS_uv). The large
container VC(I_uv) appears only in the target R^ss and in the q-pilot target
pilot class of {q_vO_v}.

Consequences:

- The correction is rejected; prior audits task-436/441/446 stand.
- S_q={q_vO_v} does not qualify as an eta^anab_S input.
- The log-shell construction's S_q^LS in VC(LS) remains undefined (IUT xi-d
  q-pilot region is in the large 1,circ U_Q, not a small-container image).
- The volume-scaling route with S in VC(I) is outside the eta domain.
- C1 remains open.

## 5. What would be a valid correction

A valid correction would need source support for changing line 2506 from
VC(LS_uv) to VC(I_uv), e.g. a later erratum or an explicit identification of
the two containers. None is in the LANA snapshot. The report consistently uses:

- S subset VC(LS_uv) for the input/integral structure;
- T subset VC(I_uv) for the target R^ss;
- {q_vO_v} in VC(I_uv) for the q-pilot target pilot.

No such identification is stated.

## 6. Conclusion

The "corrected" LANA eta domain VC(I_v) is FALSE. The exact source domain is

    S subset VC(LS_uv),

while the target R^ss and the q-pilot pilot use the large container VC(I_uv).
The prior container-mismatch verdicts are confirmed, not retracted.

S_q={q_vO_v} does not qualify as an eta^anab_S input; the replacement route
with S in VC(I) is outside the domain. C1 remains open.

No mixed/E3 profile, arbitrary S, or Lean edit was used.
target_accepted=false.
