# C9 COR3.12 UNCONDITIONAL NL — REVIEW SUMMARY

Date: 2026-10-25. Status: source theorem ACCEPTED; self-contained NL proof REJECTED.
No Lean.

## 0. Bottom line

All reviewers accept the STATEMENT of IUT III Cor3.12 and the paper-level
source theorem. The submitted natural-language 'unconditional proof' is
REJECTED as a self-contained proof from more basic accepted steps.
The decisive gap is Section 5: xi-f exact membership.

## 1. Accepted

- Cor3.12 statement: -|log Theta| in R, -|log Theta| >= -|log q|, C_Theta>=-1.
- Setup: initial Theta-data, Def3.8 pilots, packet+procession normalization.
- Theorem3.11/IPL/SHE/APT as source theorems.
- Hull definition; determinant may be omitted for log-volume comparison.
- q-pilot fixed value -|log q| is an input, not subject to Ind1/2/3.
- SHE/1-column expressibility as source property.
- Scope: no C9 normalized target, no factor d/82, no arch h_inf, no mixed/E3.

## 2. Rejected / decisive gaps

R1. Section 5 xi-f exact membership.
    Source says the construction is a construction of the input pilot
    log-volume 'perhaps only up to some sort of approximation, as a result of
    various indeterminacies'. The file converts this into exact membership
    -|log q| in R_{<=-|log Theta|}. This is an interpretation, not a source
    theorem; no signed epsilon with bound/sign is supplied.

R2. q-pilot input vs output.
    IPL/SHE link prime-strips/constructions, not the q-pilot VALUE as an exact
    possible OUTPUT log-volume. The q-pilot value is fixed input; R is a set of
    output log-volumes subject to Ind1/2/3. Object-link does not imply
    numerical value-membership.

R3. Closed loop.
    Closed loop is a source assertion (Remark3.9.5(ix)); cQ3/cQ4 give
    individual compatibility, not the composite closed loop.
    The closed loop gives simultaneous intertwinings, not q-pilot membership
    in the possible output set.

R4. Ob9-1.
    Ob9-1 says formal indeterminacies have no effect on comparability;
    it does not assert the natural bijection between domain/codomain
    log-volume sets used in the proof.

R5. Finiteness/compactness.
    Compactness of 1,circ U_{j,vQ} is source-asserted ('easily verified');
    an explicit compactness proof and the WLOG -|log Theta|<0 branch are
    needed for a self-contained proof.

R6. Ind1/Ind2 description.
    Ind1 includes D-dagger prime-strip automorphisms; Ind2 is not simply
    'tensor-factor copy/isomorphism' but Ism/order-2 actions on direct
    summands. The proof's descriptions are incomplete.

## 3. Consequence

Cor3.12 remains accepted as the IUT III source theorem.
The submitted NL file is a source-conditional exposition, not an
unconditional proof from lower-level accepted steps.
P6_can remains conditional on Cor3.12/source xi-f.
P6: OPEN. target_accepted=false. No Lean.

## 4. What would be needed

(a) Construct the closed-loop poly-isomorphisms explicitly.
(b) Prove xi-f exact membership, or derive a signed epsilon with a proved
    sign/bound (source gives neither).
(c) Prove that the IPL full-poly link of prime-strips implies the q-pilot
    VALUE is an output log-volume element.
(d) Expand Theorem3.11/Prop3.9/Remark3.9.5 enough to remove source citation.

These are essentially the IUT III proof itself; no shortcut is available.