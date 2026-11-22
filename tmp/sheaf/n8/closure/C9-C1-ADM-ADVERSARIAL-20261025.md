# C9 adversarial review of the LANA eta-reduction for C1

Task ID: task-440 / C9-C1-ADM-ADVERSARIAL-20261025. Reviewer: primespine. Date: 2026-10-25.
Object: tmp/sheaf/n8/closure/C9-C1-LANA-ETA-REDUCTION-20261025.md (84 lines).
Scope: independent adversarial review; no rewriting; no Lean/Project edits; no mixed/E3; only this file written.

## 0. Verdict

**REJECT the eta-reduction as a proof of C1.** Lemma A is correct. Lemma B is only conditional and its B2 step is not definitional in the required sense. The reduction hides the main content in `(Adm)` and then treats `(Adm)` as a technical admissibility condition, without proving it and without proving it is strictly smaller than C1. The step from `eta_q = eta^anab_{S_q}` to the existence of an output D0 with logVol(D0)=Q is also missing.

C1 remains open. This is an exact gap, not a counterexample to C1.

## 1. Lemma A: ACCEPT (with nonzero-pilot hypothesis)

Lemma A (lines 27-32): if V,W are one-dimensional real lines with distinguished nonzero pilots p_V,p_W, and f,g are linear isomorphisms with f(p_V)=g(p_V)=p_W, then f=g.

The proof is correct: every x is c p_V, and f(x)=c f(p_V)=c g(p_V)=g(x).

Caveat: the hypothesis that the pilots are **nonzero** is essential. If p_V=0 or p_W=0, the equality at the pilot says nothing. The reduction does not prove that the q-pilot class [S_q] is nonzero or even well-defined as a nonzero element of R^ss.

## 2. Lemma B: REJECT as stated; B1 conditional, B2 not definitional enough

### B1 (line 36-37)

LANA 9.2 defines eta^q with target pilot the class of `{q_v O_v}` embedded diagonally in the volume container. If the reduction's `S_q` is literally that same embedded set/class, B1 is a fair definitional identification.

Caveat: the reduction states S_q 'equivalently' as the q-pilot region in the volume container and the diagonal `{q_v O_v}`. LANA's R^ss is a quotient of **adelic measurable subsets T subset VC(I_v)**; it is not established that `{q_v O_v}` is an adelic measurable subset of VC(I_v) with the required finite/nonzero volume. Identifying the q-pilot value-group line with a subset of the log-shell volume container is exactly a compatibility step, not a definition.

### B2 (lines 39-41)

B2 says: for eta^anab_S, the target pilot is by definition the class of M=1·S in R^ss, hence for S=S_q, eta^anab_{S_q}(pilot)=[1·S_q]=[S_q].

Problems:

1. **Admissibility is missing.** LANA constructs eta^anab_S only after fixing S subset VC and using the anabelian action/integral structure. It does not assert that every subset S (in particular the q-pilot diagonal) is admissible for that construction. B2 is valid only if S_q is in the domain of eta^anab; that is `(Adm)`, not a definition.
2. **`[1·S_q]=[S_q]` needs the N-action.** LANA defines M=1·S as representing `LGP·S`. The equality of classes uses the action of 1 in N and the volume-equivalence quotient. The reduction does not verify that 1 acts trivially on the class of S_q, or that the action is defined on S_q. This is a hidden hypothesis.
3. **S_q may be zero/undefined.** If S_q is empty or has zero/infinite volume, its class may be zero or not in R^ss. Lemma A then fails or B2 is meaningless.
4. **Circularity.** S_q is defined from the q-pilot. Using S_q as the input S to eta^anab makes the comparison partly tautological: the pilot class is chosen to match by construction. The genuine content is whether the anabelian algorithm can accept this q-defined integral structure and produce the same comparison; that is exactly `(Adm)`/C1, not a consequence of the definitions.

Thus B1 can be accepted only under a separate identification of S_q with LANA's q-pilot class; B2 is conditional on `(Adm)` and the N-action, not definitional.

## 3. Section 4 conclusion: REJECT

The reduction concludes: if S_q is admissible, then Lemma A gives eta_q=eta^anab_{S_q}, hence C1.

Exact reasons for rejection:

1. **`(Adm)` is not proved.** The file itself lists measurability, N-stability, and membership in the domain of the anabelian construction as missing. It does not establish any of them. This is not a small technicality: LANA's report explicitly states that the compatibility `eta_q=eta^anab_S` is not yet reconstructed.
2. **`(Adm)` is not shown strictly smaller than C1.** The claim in §6 that `(Adm)` is 'strictly smaller than the full compatibility (9-1)' is unsupported. If S_q is defined from the q-pilot and must be accepted by the anabelian construction as an integral structure, `(Adm)` is essentially the compatibility for this specific S; it is not obviously weaker than C1. No reduction theorem is proved.
3. **ETA equality is not C1.** C1 requires an output possibility D0 in the multiradial output set O with logVol(D0)=Q. The eta equality is an equality of pointed isomorphisms of real lines R^val~>R^ss. The file does not prove that the class `[S_q]` corresponds to an actual possible output data D0 of the multiradial algorithm, nor that its log-volume is Q in the paper normalization. The bridge `eta equality => output membership` is missing.
4. **Pilot equality may be vacuous if pilots are zero/undefined.** As in Lemma A, nonzero pilots are required; the file does not prove [S_q] is a nonzero class with finite nonzero volume.
5. **Misuse of LANA 9.2.** LANA says: once S subset VC is fixed, this provides eta^anab_S; it also says Project LANA has not reconstructed the required compatibility. It does not say that the q-pilot diagonal is an admissible S, that any S is admissible, or that eta_q=eta^anab_{S_q}. The reduction attributes to LANA more than the source states.

## 4. Hidden assumptions and circularity summary

- **Hidden assumption H1**: `{q_v O_v}` is an adelic measurable subset/class of VC(I_v) with finite nonzero volume.
- **Hidden assumption H2**: S_q is N-stable and in the domain of the anabelian eta construction.
- **Hidden assumption H3**: `1·S_q` has the same class as S_q in R^ss.
- **Hidden assumption H4**: eta equality for the class [S_q] yields an actual possible output D0 with logVol(D0)=Q.
- **Circularity**: S_q is chosen from the q-pilot, so pilot matching is engineered. The real question is whether the anabelian construction accepts S_q as an integral structure. That is not proved.

None of H1-H4 follows from LANA 9.2 as quoted. They are precisely the remaining C1 issue.

## 5. Accept/reject table

| item | verdict | reason |
|---|---|---|
| Lemma A | ACCEPT | correct for nonzero pilots; nonzero not proved for S_q |
| Lemma B1 | CONDITIONAL | plausible definitional identification, but S_q subset VC/measurability/finite volume unproved |
| Lemma B2 | REJECT | admissibility and N-action/1·S_q class not proved; pilot may be zero |
| §4 implication (Adm)=>C1 | REJECT | (Adm) unproved; eta equality != output membership; no strict reduction |
| §5 'Adm strictly smaller' | REJECT | unsupported; may be equivalent to C1 compatibility |
| §6 progress claim | REJECT | only Lemma A is rigorous; B and the bridge are conditional |

## 6. What would be needed

1. Prove S_q is an adelic measurable N-stable subset/class of VC(I_v) with finite nonzero volume (H1/H2/H3).
2. Prove the anabelian eta construction accepts S_q and yields eta^anab_{S_q} with the same pilot (or prove `(Adm)` from source, not assume it).
3. Bridge eta equality to an actual possible output D0 in O with logVol(D0)=Q in the paper packet+procession normalization.
4. If claiming reduction, prove `(Adm)` is strictly weaker than C1; otherwise C1 remains equivalent to the eta problem.

## 7. Final review verdict

**REJECT the eta-reduction as a C1 proof.** Lemma A is correct. Lemma B is conditional and B2 hides admissibility/N-action/volume hypotheses. The reduction does not establish `(Adm)`, does not show it is smaller than C1, and does not bridge eta equality to output data membership. C1 remains open; LANA 9.2 does not supply the missing compatibility. No mixed/E3; no Lean.

target_accepted=false.
