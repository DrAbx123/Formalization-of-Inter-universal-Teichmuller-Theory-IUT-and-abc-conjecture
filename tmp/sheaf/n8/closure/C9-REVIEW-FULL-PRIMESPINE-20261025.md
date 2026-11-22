# C9 independent full-proof review of C9-P6-CAN-NATURAL-PROOF

Task ID: task-415 / C9-REVIEW-FULL-PRIMESPINE-20261025. Reviewer: primespine. Date: 2026-10-25.
Object of review: tmp/sheaf/n8/closure/C9-P6-CAN-NATURAL-PROOF-20261025.md (162 lines).
Scope: independent natural-language reread; no rewriting; no Lean/Project edits; no mixed/E3; only this file written.

## 0. Verdict

**REJECT as a complete proof of P6_can.** The proof is a useful conditional skeleton, but two central steps (A2, A3) are not justified by the cited source at the required exactness. A1 is essentially acceptable as a source-input statement; T_can is definitional. The theorem does not follow from the accepted steps.

## 1. A1 (q-pilot input): ACCEPT with a minor caveat

Proof lines 32-48. A1 states that the q-pilot F^value x mu-prime-strip at (1,0) is a fixed coric input, Q_can=-|log q| is not subject to Ind1/2/3, and the output is linked to it by full poly-isomorphisms.

Reasons to accept: Definition3.8(i) does determine the q-pilot object by generators up to torsion, and Definition3.8(ii) makes the LGP-link a full poly-isomorphism. The distinction F^value full poly vs F^unit x mu Ind1/2/3 is source-consistent.

Minor caveat: 'rigidified by the 1-column arithmetic holomorphic structure' (line 44) is a summary of Remark3.11.1(ii); it is not an additional proof. This is acceptable only as a source-input convention, not as a construction of an explicit q-pilot.

## 2. A2 (determinant/log-volume comparison): REJECT as stated

Proof lines 50-72. A2 asserts a single arithmetic vector bundle E_H of rank>1 such that

    L_H = det^tensor M(E_H) tensor det^tensor M(O(-))^{-1},
    deg(L_H)/M = deg(det E_H) = mu_log(H(C)) = h_can.                 (2.1)

and deg(L_q)=Q_can.

Exact reasons for rejection:

1. **No single E_H is constructed.** Source Step (xi-c)/(xi-d) (IUT III lines 10620-10681) yields a *collection of possible output data* expressed in terms of localizations of arithmetic vector bundles of rank>1. The proof silently replaces the collection by one arithmetic vector bundle E_H. The existence and choice of E_H are exactly the source gaps G1-G7 recorded in C9-P6-CAN-CHAIN.
2. **The determinant identity is not source-proved.** Source says one takes 'a suitable positive tensor power of the determinant' and applies a 'suitably normalized' log-volume; it does not prove the equality (2.1) for a global arithmetic vector bundle E_H. The `O(-)` inverse-determinant factor and its degree are introduced by the proof without a source construction.
3. **`deg(O(-))=0` is asserted, not derived.** Line 67 cites Prop3.9(i), but the normalization of `O(-)`/its arithmetic degree is not established in the proof. If `O(-)` is the source line bundle, its degree need not be zero without the normalization argument.
4. **The common-rescaling sentence (lines 70-72) is not a proof of equality.** A common rescaling of a normalization convention can preserve an inequality but cannot establish the exact identity h_can=mu_log(H(C)); the identity is the missing content.

The source-level conclusion required for A3 is only the construction of a comparable output collection and a normalized log-volume. A2's exact determinant equality is stronger than the source text and is unsupported.

## 3. A3 (q-pilot value in the Theta-pilot output set): REJECT as stated

Proof lines 74-127. A3 asserts Q_can in R_{<=h_can} via five steps: formal quotient, sQ3/sQ4, closed loop, the AND, log-volume.

Exact reasons for rejection:

1. **The source explicitly qualifies the key step by 'perhaps only up to some sort of approximation'.** IUT III Step (xi-f) (lines 10705-10715) says the construction of output possibilities constitutes a construction of the input pilot-object log-volume 'perhaps only up to some sort of "approximation", as a result of various indeterminacies', and only then states that the inclusion follows formally. A3 ignores this qualification and asserts exact membership `Q_can in R_{<=h_can}`. The gap between approximate and exact membership is not resolved anywhere in A3.
2. **The 'closed loop' is asserted, not constructed.** Step (3), lines 97-105, says the chain of poly-isomorphisms 'forms a closed loop' by Remark3.9.5(ix), but does not exhibit the maps, check their composition, or prove that the q-pilot value is recovered. The source's closed loop is a qualitative construction-computation, not an exact numerical identity.
3. **Step (5) is circular.** Lines 118-126 say 'the q-pilot log-volume is the projection/special case of the Theta-pilot output log-volume under the same indeterminacy quotient. Hence Q_can in R_{<=h_can}.' That is precisely the conclusion A3 is supposed to prove; the preceding closed-loop/AND discussion does not independently establish it.
4. **The AND/subquotient manipulation (lines 107-116) is formal, not numerical.** `(q-itw) => (q-itw AND Theta-itw/indets) => (Theta-itw/indets)` is a logical rewriting; it does not prove that the q-pilot log-volume lies in the hull's possible-output set, nor does it resolve Ind1/2/3.
5. **The set R_{<=h_can} is defined by the inequality.** By definition `R_{<=h_can}={lambda | lambda<=h_can}`. Establishing membership is exactly establishing the inequality; A3 cannot use the definition as a substitute for the missing exact-membership argument.

Thus A3 is not a proof of the source's exact inclusion; at best it restates the source's approximate closed-loop argument without resolving the approximation.

## 4. T_can: ACCEPT only as a target definition

Proof lines 129-136. T_can asserts C9Hull=IIIHull and C9QPilot=IIIQPilot. This is a definitional identification of the paper target, not a theorem. It is acceptable for defining P6_can, but it cannot repair A2/A3: if A2/A3 are not proved, T_can only says which unproved objects the target refers to.

## 5. The theorem (lines 138-146): DOES NOT FOLLOW

The theorem is obtained by combining A1, A2, A3. A1 is acceptable; A2 and A3 are rejected. Therefore the implication

    A1 + A2 + A3 => Q_can <= h_can

is logically valid as a conditional, but the premises A2/A3 are not established. P6_can is **not proved** by this file.

Circularity summary:

- A2 assumes a single E_H/determinant identity that the source only constructs as a collection;
- A3 assumes the closed loop produces exact q-pilot membership, which is the desired conclusion;
- T_can is a definition, not an independent bridge.

No step of A2/A3 is an immediate source quotation at the exact strength used. The source itself flags an approximation in the crucial A3 step.

## 6. What would be accepted

Accept the proof as a **conditional schema**: if A2's determinant/log-volume identity and A3's exact membership (including the Ind1/2/3 resolution) were supplied, the theorem would follow. Accept A1 as source-input and T_can as target definition. Reject the claim 'P6_can natural-language proof completed' (line 161) and the final 'P6_can holds' conclusion (lines 140-146) as not justified.

Required exact fixes (not supplied here):

- A2: construct the global E_H (or a canonical collection) and prove (2.1) from the source determinant/normalized log-volume construction; justify the O(-) factor/degree;
- A3: resolve the `perhaps only up to approximation` clause in Step (xi-f) to an exact inclusion, or state P6_can only up to the source approximation; construct and verify the closed-loop maps;
- make the Ind1/2/3 quotient compatible with the numerical log-volume readout at the exact level needed for membership.

## 7. Final review verdict

**REJECT full proof; ACCEPT conditional skeleton and A1/T_can only.** P6_can does not follow from the reviewed file as written. The exact blockers are A2's unsupported global determinant identity and A3's unsupported exact membership (source approximation caveat and circular closed-loop step). No normalized surrogate/mixed/E3 is used in this review; no Lean.

target_accepted=false.
