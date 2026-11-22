# C9 adversarial review of the volume-scaling route to C1

Task ID: task-445 / C9-C1-VOL-ADVERSARIAL-20261025. Reviewer: primespine. Date: 2026-10-25.
Object: tmp/sheaf/n8/closure/C9-C1-VOLUME-SCALING-20261025.md (80 lines).
Scope: independent adversarial review; no rewriting; no Lean/Project edits; no mixed/E3; only this file written.

## 0. Verdict

**REJECT the volume-scaling route as a proof of C1.** It is a conditional construction under an unproved and structurally doubtful constant-Jacobian hypothesis (H1), plus unproved non-atomicity/volume-existence, admissibility, pilot nonzero/finite-volume, and the eta-to-output bridge. The route does not reduce C1 to strictly smaller gaps: G1 and G3 reintroduce the same LGP/anabelian compatibility, and G5 is C1.

The only rigorous component is the elementary measure-existence lemma under its stated hypotheses; Lemma A is correct only for nonzero pilots, which are not established here.

## 1. H1 (constant Jacobian T_1): REJECT as unproved and suspect

H1 assumes T_1: VC(LS) -> VC(I), S -> 1·S, is a measurable bijection onto its image with constant Jacobian J>0, so vol(T_1(S))=J vol(S).

Exact reasons:

1. **No source theorem.** LANA's N-action/LGP action on log-shells is constructed anabelianly, with (Ind1),(Ind2) and only upper semi-compatibility (Ind3) along the log sequence. It is not asserted to be a set-theoretic measurable bijection with constant Jacobian.
2. **APT conflict.** LANA/Theorem3.11 explicitly warn that this is a construction algorithm, not a set-theoretic transport. Modeling T_1 as a measurable bijection with a global constant J is exactly the set-theoretic transport the source avoids.
3. **Locality/weights.** The LGP action is local at v in V and involves products of local log-shells with different normalizations/weights N_v. A single global constant Jacobian J independent of v, of the compact structure, and of Ind3 is not source-supported.
4. **Non-injectivity/non-surjectivity.** The log-Kummer comparison is only upper semi-compatible; images may be nested/subset, not a bijection onto the whole target. H1 is stronger than the source's comparison.

H1 is therefore not a technical gap that 'may be provable from Haar'; it is a new hypothesis that changes the problem.

## 2. Lemma B (volume existence): CONDITIONAL, not proved

Lemma B: if VC(LS) has measurable subsets of every volume in (0,vol_total), then for V_q/J there is measurable S with vol(S)=V_q/J.

Problems:

1. **Non-atomicity is asserted.** The measure on VC(LS) is a Haar/log-volume measure on a p-adic product of log-shells; non-atomicity is plausible but not proved in the file. If the measure has atoms, not every intermediate volume is attained.
2. **Finite total volume and range are not checked.** The proof needs V_q/J < vol_total and a finite non-atomic measure. Neither is established.
3. **Adelic/measurable conditions.** Even if a set of the right volume exists, it must be adelic/measurable and in the domain of the anabelian construction; Lemma B gives only a measurable volume, not an admissible S.
4. **Choice depends on q.** S is chosen using V_q, i.e. from the q-pilot. This is the same engineered-pilot circularity as the S_q route; it does not prove the anabelian algorithm accepts the q-defined region.

Lemma B is acceptable only as an abstract measure lemma, not as a construction of the required S.

## 3. G3 (admissibility/integral structure): REJECT as missing

Volume matching does not imply S is admissible for eta^anab. LANA fixes S subset VC and then constructs eta^anab_S using the action and S as integral structure; it does not say every measurable S is admissible. G3 includes:

- S is adelic and in the correct volume container;
- S is N-stable/compatible with the LGP action;
- S lies in the domain of the anabelian construction.

None is proved. The route's claim that 'S chosen by volume respects the LANA domain' is unsupported: choosing S by volume in VC(LS) does not ensure it is an integral structure. This is the same admissibility gap as the previous S_q route, only moved to a different S.

## 4. G4 (pilot nonzero/volume class): PARTIAL/REJECT

The route assumes V_q>0 and [T_1(S)]=[S_q] in R^ss. Missing:

1. `S_q` has finite positive volume in the large container. The q-pilot class {q_v O_v} embedded diagonally need not have finite volume in the large container without a source argument.
2. The pilot class [S_q] is nonzero in the pointed real line. V_q>0 is not sufficient: the zero of the pointed real line is a class determined by the volume normalization; one must prove [S_q] is not that class.
3. `T_1(S)` is adelic measurable and its class is in R^ss. H1 supplies a map but not the adelic class compatibility.

Without nonzero pilots, Lemma A cannot be applied.

## 5. G5 (bridge eta equality -> output membership): REJECT; this is C1

The route itself states that even if eta_q=eta^anab_S, one still needs

    (Bridge) eta equality -> exists output D0 in O with logVol(D0)=Q.

This bridge is exactly C1. LANA's eta equality is an equality of pointed isomorphisms R^val~>R^ss; it does not by itself produce a possible output data element D0 of the multiradial algorithm, nor identify its log-volume with Q in the paper packet+procession normalization. The volume-scaling route therefore does not reduce C1 to anything smaller: it leaves G5, which is the original existence/membership problem.

## 6. LANA 9.2 misuse and circularity

- LANA 9.2 does not provide a constant-Jacobian N-action. It says the anabelian action is constructed after fixing S, subject to Ind1/Ind2, with only upper semi-compatibility (Ind3) at the output stage.
- The route chooses S by matching the q-pilot volume; the pilot equality is then engineered. The substantive question remains whether S is admissible and whether the anabelian construction realizes the q-pilot output. That is C1.
- The route's claim 'this respects the LANA domain' is the opposite of what needs proof: VC(LS) is the small container, while the q-pilot class is in the large container; T_1 is assumed to bridge them, but no source constructs such a bridge with constant volume scaling.

## 7. Accept/reject table

| gap | verdict | exact reason |
|---|---|---|
| H1 constant Jacobian T_1 | REJECT | no source; APT says not set-theoretic; local weights/Ind3; bijection unproved |
| Lemma B non-atomic/volume | CONDITIONAL | non-atomicity/finite range/admissibility unproved |
| G3 admissibility | REJECT | volume matching does not make S N-stable/integral/adelic |
| G4 pilot volume/nonzero | REJECT | S_q finite positive/nonzero class unproved |
| G5 bridge | REJECT | this is C1; eta equality does not give output D0 |
| Lemma A | ACCEPT conditionally | correct only with nonzero pilots; nonzero not established |

## 8. What would be needed

1. Replace H1 by a source-valid description of the LGP action/Ind3 and prove the exact volume comparison at the level of adelic classes.
2. Prove non-atomicity/finite total volume and find an **admissible** S, not merely a measurable one.
3. Prove S_q has finite positive volume and nonzero pilot class; prove T_1(S) is in R^ss and has the same class.
4. Prove G5 (eta equality -> output membership) or show the route does not claim C1.

## 9. Final review verdict

**REJECT the volume-scaling route as a C1 proof.** H1 is an unproved set-theoretic constant-Jacobian hypothesis in tension with APT/Ind3; Lemma B is conditional; G3/G4 are missing; G5 is C1 itself. C1 remains open. No mixed/E3; no Lean.

target_accepted=false.
