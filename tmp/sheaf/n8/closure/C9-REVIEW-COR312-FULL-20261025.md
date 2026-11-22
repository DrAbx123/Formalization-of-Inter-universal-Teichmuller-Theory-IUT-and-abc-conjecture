# C9 independent full reread of the unconditional Cor3.12 NL proof

Task ID: task-423 / C9-REVIEW-COR312-FULL-20261025. Reviewer: primespine. Date: 2026-10-25.
Object: tmp/sheaf/n8/closure/C9-COR312-UNCONDITIONAL-NL-20261025.md (196 lines).
Scope: independent natural-language review; no rewriting; no Lean/Project edits; no mixed/E3; only this file written.

## 0. Verdict

**REJECT the claim that the file proves Cor3.12 unconditionally.** The proof is a faithful source-level sketch of IUT III Cor3.12, and most steps are acceptable as citations of Theorem3.11/Remark3.9.5/Prop3.9. However the decisive Step 5 (closed loop/approximation) is not an exact proof: it interprets the source's 'perhaps only up to some sort of approximation' as the indeterminacy quotient without proving that no numerical/volume loss occurs, and then asserts the q-pilot membership that is precisely the desired conclusion. Therefore the final inclusion and the 'unconditional' conclusion do not follow from the text as written.

Accept: Setup, A1/q-pilot fixedness, hull/log-volume Ob3-3, finiteness citation.
Reject: exact closed-loop/approximation step; unconditional conclusion.

## 1. Per-step review

### 1.1 Theorem/setup (lines 6-39): ACCEPT

The statement matches IUT III Cor3.12. The q-pilot object is correctly described via Definition3.8(i) up to torsion, and the LGP-link via Definition3.8(ii) as a full poly-isomorphism. The normalization is the paper's packet+procession normalization. No hidden normalization is introduced.

### 1.2 Theorem3.11/IPL/SHE/APT (lines 41-64): ACCEPT as source citation

The proof cites, rather than re-proves, Theorem3.11 and Remark3.11.1. Its descriptions of (Ind1)-(Ind3), IPL, SHE, APT and HIS are source-consistent. This is a legitimate source input; no black box beyond accepting the cited paper theorem.

### 1.3 Hull/log-volume/Ob3-3 (lines 66-91): ACCEPT with a wording caveat

The hull operation and the determinant/log-volume comparison are correctly attributed to Remark3.9.5 and Ob3-3. Ob3-3 does say the determinant intermediate may be omitted when only log-volumes are concerned. The compactness/finiteness reference is source-supported.

Caveat: the file says 'By Ob3-3 ... the arithmetic degree of the determinant line bundle is, with suitable normalization, the log-volume of the original arithmetic vector bundle.' This is an acceptable source paraphrase, but it is not a construction of a global E_H; the review does not treat it as proving an exact global determinant identity.

### 1.4 Fixed q-pilot/SHE (lines 93-113): ACCEPT as far as linkage

The q-pilot is fixed and not subject to Ind1/2/3; IPL links output data to it. This is source-consistent (xi-a/b, xi-e). What is established here is a **linkage**, not yet membership of -|log q| in the output log-volume set.

### 1.5 Closed loop/formal quotient (lines 115-158): REJECT as an exact step

This is the decisive step. The proof lists a chain

    q-pilot (codomain) -> LGP-link -> sQ1/sQ2 -> sQ3/sQ4 -> q-pilot,   (1.1)

and says 'By Remark3.9.5(ix), the above chain forms a closed loop.' It then concludes that the closed loop 'exhibits the q-pilot object as one of the possible output data', hence -|log q| in R_{<=-|log Theta|}.

Exact reasons for rejection:

1. **The closed loop is asserted, not constructed.** The proof does not exhibit the intermediate poly-isomorphisms or verify that the composite returns to the q-pilot object. Remark3.9.5(ix) is a qualitative source discussion of the subquotient operations; it does not, as written here, establish the specific closed loop (1.1) at the exact object level.
2. **The source's approximation caveat is not resolved.** Step (xi-f) (IUT III lines 10705-10715) says the construction of output possibilities constitutes a construction of the input pilot-object log-volume 'perhaps only up to some sort of "approximation", as a result of various indeterminacies'. The proof says: 'the approximation is precisely the indeterminacy quotient just described, not an additional numerical error' (lines 148-151). This identification is an **interpretive assertion**, not proved. The source's 'perhaps' and 'some sort of' do not establish that the quotient preserves the exact log-volume value; no estimate or exact quotient computation is supplied.
3. **The q-pilot-as-possible-output claim is stronger than the source.** The source says the construction of output data possibilities constitutes a construction of the input log-volume; it does not explicitly say that the q-pilot object itself is one of the possible output data. The proof uses that stronger statement to obtain membership. This is the gap, not a formal consequence.
4. **Ob9-1 is overstated.** The proof says realified semi-simplification 'induces a natural bijection between log-volumes of hulls in domain and codomain' (lines 143-144). Source Ob9-1 says the formal indeterminacies have no effect on comparability and function as compatibility conditions when passing to coarse invariants; it does not assert a natural bijection of log-volume sets. The bijection is an additional claim.
5. **Circularity.** Lines 153-158 conclude -|log q| in R_{<=-|log Theta|} because 'the closed loop exhibits the q-pilot object as one of the possible output data'. But being one of the possible output data/log-volumes is exactly what the inclusion asserts. The closed-loop discussion is supposed to produce it; instead it assumes it.

### 1.6 Inequality/C_Theta (lines 160-170): CONDITIONAL

If the membership -|log q| in R_{<=-|log Theta|} is granted, the inequality and C_Theta>=-1 follow by definition. This step is formally correct but inherits the Step 5 gap.

### 1.7 Summary/unconditionality (lines 172-196): REJECT

The claim 'Corollary 3.12 holds unconditionally over admissible initial Theta-data' does not follow. The proof has a hidden semantic hypothesis: the source's approximate construction is exactly the indeterminacy quotient and yields exact membership. Until that is proved (or the theorem is stated with the approximation), the NL proof is conditional on the source's xi-f formal conclusion.

## 2. Circularity and hidden hypotheses

- Circularity: Step 5 assumes the q-pilot is one of the possible output data in order to prove its log-volume is in the output set.
- Hidden hypothesis: the interpretation of 'perhaps only up to approximation' as 'exactly modulo Ind1/2/3, with no numerical loss'.
- Hidden strengthening: 'linked by full poly-isomorphism' is promoted to 'one of the possible output data'; linkage is not membership.
- The proof relies on Theorem3.11/Remark3.9.5 as source black boxes; this is allowed for a source-level proof, but then the xi-f approximation cannot be silently upgraded to exactness.

## 3. Does Cor3.12 follow unconditionally?

From the reviewed file, **no**. The source-level theorem is stated as paper Cor3.12, and a proof sketch follows the source, but the only step that converts the construction into the numerical inclusion is the closed-loop/approximation step, and that step is asserted rather than proved. The file therefore establishes a conditional schema:

    [Theorem3.11 data + exact xi-f closed-loop membership] => Cor3.12.

It does not establish Cor3.12 unconditionally from the accepted steps.

## 4. Required exact fixes (not supplied here)

1. Construct the closed-loop poly-isomorphisms explicitly and verify the composite returns to the q-pilot object.
2. Prove that the indeterminacy quotient in xi-f preserves the exact log-volume value (or state the theorem only up to the source approximation).
3. Justify the step from 'linked by full poly-isomorphism' to 'q-pilot is one of the possible output data', or replace it with a weaker exact statement.
4. Remove the unproved 'natural bijection' claim from Ob9-1 unless separately proved.

## 5. Final review verdict

**REJECT unconditional; ACCEPT conditional/source-level sketch only.** Cor3.12 does not follow unconditionally from the reviewed NL proof as written. The exact blockers are the unconstructed closed loop and the unresolved xi-f approximation/exact-membership step. No Lean, no mixed/E3, no normalized surrogate used in this review.

target_accepted=false.
