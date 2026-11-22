# C9 C1 eta-reduction: audit of LANA eta domain/admissibility

Task: task-436. Date: 2026-10-25. Author: transport.
Audit of C9-C1-LANA-ETA-REDUCTION-20261025.md against LANA report 9.2.
No Lean; no mixed/E3; no arbitrary. Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-C1-LANA-ETA-REDUCTION-20261025.md | 84 | BEC10323DE5F0DECCB04F359EAB7535D8DF3983EAF74EBEC91076D1C62FAE067 |
| C9-STRICT-DEFICIT-LANA-SNAPSHOT-20261024.tex | 2726 | 3E613BEE63EFBFA7B17178566DD837D1CD92ED21491EC6E65D534B3521FC58BF |

The LANA snapshot is the local source for report 9.2. Relevant lines:

- volume containers: lines 1538-1590;
- eta algorithm: lines 2426-2499;
- main goal/eta comparison: lines 2502-2523;
- eta minimal structure: lines 2525-2539.

## 1. Verdict

The reduction is REJECTED.

LANA 9.2 does NOT define eta^anab_S for every subset S of the volume
container VC(I_v). The stated domain is

    S subset VC(LS_uv),

the log-shell version of the volume container at uv, and the target R^ss is
the quotient of adelic measurable subsets of VC(I_uv).

The candidate S_q={q_v O_v} does NOT qualify as an S in this domain: q_v O_v is
the q-pilot fractional ideal, and LANA places its class in the **large**
volume container VC(I_uv) as the target pilot of eta_q (lines 2515-2517), not
as a subset S of the **small/log-shell** volume container VC(LS_uv) used to
define eta^anab_S (lines 2503-2513).

Therefore:

- Lemma A of the reduction (linear maps equal if they agree at a pilot) is
  valid.
- Lemma B (the pilot class of eta^anab_{S_q} equals the q-pilot class) is NOT
  justified: eta^anab_{S_q} is not defined by LANA 9.2.
- The reduction C1 <= (Adm) is not valid as stated; the missing condition is
  not merely measurability/N-stability, but the wrong container for S_q.

## 2. Exact LANA 9.2 domain

Lines 2502-2517:

    Once we fix S subset VC(LS_uv), this provides an isomorphism between
    the C part of the original BPS (denoted R^val) and the C constructed
    using the action and S as the integral structure, denoted R^ss; more
    precisely,

        R^ss = {T subset VC(I_uv) | adelic and measurable} / ~,       (2.1)

    where T ~ T' iff the volume of T coincides with that of T'; we define
    M=1·S (the action of 1 in N), which represents "LGP·S", and put the
    class of M in R^ss to be the pilot.

    Thus the isomorphism

        eta^anab_S : R^val ~> R^ss                            (2.2)

    of pointed real vector spaces depends on S, and is constructed via
    anabelian methods as discussed above.

Exact domain facts:

(D1) S is a subset of VC(LS_uv), the log-shell/small volume container.
     It is NOT an arbitrary subset of the large container VC(I_uv).

(D2) R^ss is a quotient of adelic measurable subsets T of VC(I_uv) by
     volume equality. Thus the target class [1·S] must be adelic and
     measurable in the large container.

(D3) The eta algorithm itself (lines 2455-2499) starts from a BPS and a
     fixed isomorphism to a Theta-pilot BPS of a Hodge theater; the
     N-action is constructed anabelianly and is subject to Ind1/Ind2
     (line 2503). The report does not state that every subset
     S subset VC(LS) is admissible; it says "once we fix S ... this
     provides an isomorphism."

(D4) The report does not explicitly state an N-stability condition on S.
     What it does require is that S lies in the log-shell container and
     that its class [1·S] lies in R^ss (adelic measurable). Additional
     compatibility of S with the N-action is part of the anabelian
     construction, but the exact admissibility predicate is not spelled
     out beyond these points.

Thus the answer to the task question:

    eta^anab_S is NOT defined for every S subset VC(I_v).
    Its source domain is S subset VC(LS_uv) with [1·S] adelic measurable
    in R^ss; N-stability is not explicitly stated, but the N-action/
    anabelian construction is required.

## 3. Does S_q={q_v O_v} qualify?

No.

LANA 9.2, lines 2515-2517:

    when we work with a BPS that was constructed as the q-BPS of a Hodge
    theater, this perspective provides an isomorphism

        eta^q : R^val ~> R^ss,                                  (3.1)

    where the pilot of the target R^ss is given by the class of
    {q_uv O_uv} embedded "diagonally" into the large volume container
    VC(I_uv).

This is the **eta_q side**: the q-pilot target class is the class of q_vO_v in
the large container VC(I_uv). It is not a choice of S for eta^anab_S.

The S in eta^anab_S is a subset of VC(LS_uv), the log-shell/small container.
q_vO_v is a fractional ideal (an arithmetic line bundle object); it is not a
subset of the log-shell container. The report uses q_vO_v specifically for the
target pilot of eta_q, not as an integral structure S inside the eta algorithm.

Therefore:

- eta^anab_{S_q} is not defined by LANA 9.2.
- The pilot equality in Lemma B,
      eta^anab_{S_q}(pilot of R^val) = [1·S_q] = [S_q],
  cannot be asserted.
- Even if one tried to embed S_q={q_vO_v} diagonally into the small
  log-shell container, that embedding is not the LANA construction and is not
  shown to be adelic/measurable or compatible with the N-action.

## 4. Step-by-step audit of the reduction

### Lemma A — ACCEPT

Lemma A: if V,W are one-dimensional pointed real lines and f,g are linear
isomorphisms with f(p_V)=g(p_V)=p_W, then f=g. This is correct and
elementary. It is independent of the LANA domain issue.

### Lemma B — REJECT

Lemma B asserts:

    eta_q(pilot R^val) = [S_q],
    eta^anab_{S_q}(pilot R^val) = [1·S_q] = [S_q].

The first equality is source (eta_q target pilot is [q_vO_v] in large
VC(I), lines 2515-2517). The second is NOT source: S_q is not an admissible S
in the domain of eta^anab_S (Section 2-3 above). The notation
eta^anab_{S_q} is undefined in LANA 9.2.

Thus Lemma B is not proved. Its conclusion "the two maps have the same value
at the pilot" fails at the definitional level.

### Conclusion under admissibility — REJECT

The reduction says: if S_q is admissible for the eta algorithm, then Lemma A
applies and eta_q=eta^anab_{S_q}. This conditional is formally valid
**provided** eta^anab_{S_q} is defined and both maps are pointed linear
isomorphisms. But:

- S_q is not shown admissible; indeed S_q is in the wrong container.
- The condition (Adm) proposed in the reduction ("S_q measurable, N-stable,
  in the domain") is not the exact LANA domain condition: it omits the
  log-shell container condition and the adelic-measurable target condition.
- No construction of an admissible S representing the q-pilot class in
  VC(LS) is provided.

Therefore the reduction C1 <= (Adm) is not established; the proposed (Adm) is
both unproved and insufficient as stated.

### Section 6 progress claim — REJECT

The reduction is not a valid separation because Lemma B fails. The only
remaining statement is the original C1-style membership, not a smaller
admissibility condition.

## 5. What would repair the reduction

A valid eta-reduction would need:

(R1) an exact LANA domain statement: S subset VC(LS_uv) and [1·S] adelic
     measurable in R^ss; plus whatever compatibility with the anabelian
     N-action/Ind1/Ind2 is required;

(R2) a constructed admissible S_q^ad in that domain, not the q-pilot
     fractional ideal q_vO_v itself;

(R3) a proof that the pilot class of eta^anab_{S_q^ad} equals the q-pilot
     target class [q_vO_v] in the large container, including the
     small-to-large container comparison;

(R4) proof that eta^anab_{S_q^ad} is a pointed linear isomorphism (the LANA
     construction gives an isomorphism of pointed real lines only under its
     domain hypotheses).

None of R1-R4 is in the reduction. In particular, the reduction's S_q is the
eta_q target object, not an eta^anab input.

## 6. Conclusion

The LANA 9.2 domain is

    S subset VC(LS_uv),   [1·S] adelic measurable in R^ss,

not arbitrary S subset VC(I_v). N-stability is not explicitly stated in the
report; the anabelian N-action compatibility is part of the construction.

The candidate S_q={q_v O_v} does NOT qualify: q_vO_v is the q-pilot fractional
ideal, used as the target pilot of eta_q in the large container VC(I_uv), not
as a subset S of the log-shell container VC(LS_uv) defining eta^anab_S.

Accordingly:

- Lemma A: ACCEPT.
- Lemma B: REJECT.
- Reduction C1 <= (Adm): REJECT.
- C1 remains open; the eta-reduction does not reduce it to a correct
  admissibility statement.

No mixed/E3 profile, arbitrary S, or Lean edit was used.
target_accepted=false.