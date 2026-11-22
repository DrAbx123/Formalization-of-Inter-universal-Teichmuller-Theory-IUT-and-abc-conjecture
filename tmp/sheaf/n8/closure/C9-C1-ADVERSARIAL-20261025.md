# C9 adversarial review of C1 derivations

Task ID: task-435 / C9-C1-ADVERSARIAL-20261025. Reviewer: primespine. Date: 2026-10-25.
Assumptions: A1=Theorem3.11, A2=Proposition3.9, A3=Remark3.9.5. No extra assumptions; no Lean/Project edits; no mixed/E3; only this file written.

## 0. C1 and the question

C1 (compatibility/xi-e/xi-f):

    there exists an output possibility D0 in O (modulo Ind1/2/3)
    such that logVol(D0) = Q := -|log q|.                          (0.1)

Equivalently Q in R_possible := {logVol(D) | D in O}. The derivations to review are the direct APT/SHE/IPL route, the closed-loop route, local exact+sum, closure/limit, determinant line bundle, APT fixed point, L1-L3, and fitw/subquotient AND.

**Verdict: no reviewed route derives C1 from A1-A3. C1 remains an independent source assertion/compatibility lemma. It is not disproved (the source asserts it), but it is not a consequence of the three assumptions as stated.**

## 1. What A1-A3 actually give

A1 gives: the multiradial algorithm, output data O, IPL links output prime-strips to the fixed q-pilot input, SHE expressibility relative to the 1-column structure, APT as a construction algorithm (not a set-theoretic map), and Ind1/2/3.

A2 gives: Q=logVol(q-pilot), h=logVol(H), the packet+procession log-volume, monotonicity.

A3 gives: the holomorphic hull H of O, Ob1-Ob9, determinant/log-volume comparison, formal quotient/closed-loop discussion; it gives the **upper bound**

    R_possible subset {x | x <= h}.                                (1.1)

None of A1-A3 contains an existence/surjectivity axiom of the form 'some output D has logVol(D)=Q'. The q-pilot value Q is an **input** value; D is **output** data. A link between input and output prime-strips does not by itself produce a numerical output element with the same log-volume.

## 2. Adversarial review per route

### R1. Direct APT/SHE/IPL route (C9-COR312-FROM-ASSUMPTIONS §3): REJECT

The route says APT/SHE/IPL plus 'the construction includes a construction of Q' implies a D0 in O with logVol(D0)=Q. This is precisely the missing step, restated. APT explicitly is not a set-theoretic region map; SHE is expressibility under the condition that the input value be Q; IPL links prime-strips, not values. None yields an output element D0. The route is circular: it assumes an output representing Q in order to conclude Q is an output.

### R2. Closed loop/cQ3/cQ4 route: REJECT

The closed-loop chain q-pilot -> LGP -> sQ1/sQ2 -> sQ3/sQ4 -> q-pilot is asserted, not constructed. Even if it closes at the level of F^⊩▶×μ-prime-strips, it yields simultaneous intertwinings (q-itw and Theta-itw up to Ind), not a numerical membership logVol(D0)=Q. The step 'the q-pilot log-volume is the projection/special case of the Theta-pilot output log-volume' is the desired conclusion; it is circular. The source's 'perhaps only up to some sort of approximation' is not an exact existence statement.

### R3. Local exact comparison + sum (Strategy A): REJECT as a derivation of global C1

Local arithmetic may give a plausible exact local volume logVol(U_v)=Q_v from theta ratios, but the route needs all of:

1. U_v is a possible output packet of the **global** multiradial algorithm (local part of Theorem3.11; not proved);
2. the local packets glue/product to an actual global output D0 (an independence/product compatibility not in A1-A3);
3. the global weights/procession normalization/arch/good places sum to Q (additional normalization choices);
4. q_v up to torsion is compatible with the global q-pilot object.

None of these follows from A1-A3. The local exact equality is not global C1. This route also risks treating `q_v` as a scalar when only the q-pilot object up to torsion is canonical.

### R4. Closure/limit + compactness (Strategy B): REJECT

The source's approximation is not a proved limit with a sign/bound. The route assumes approximating outputs arbitrarily close to Q and closedness/continuity of R_possible, but A2/A3 do not prove R_possible closed, log-volume continuous on the relevant Ind quotient, or that a limit of possible values is possible. A limit point of a set need not belong to it. No source epsilon/sign exists; choosing one is arbitrary.

### R5. Determinant line bundle exact degree (Strategy C): REJECT

The route requires a global E_H and an isomorphism L_H = det^M(E_H) tensor det^M(O(-))^{-1} isomorphic to L_q in the global Frobenioid, with exact normalization. A2/A3 only give a determinant/log-volume comparison 'with suitable normalization', not an object-level isomorphism. The E_H/det/O(-)/M details are exactly the open A2 gaps; assuming L_H≅L_q is assuming the value membership, not deriving it.

### R6. APT fixed point (Strategy D): REJECT

No map F on log-volumes is defined; APT is a construction algorithm, not a set-theoretic function with a fixed point. The statement 'constructs its input' is informal. No fixed-point/image theorem is available.

### R7. L1/L2/L3 route (C9-SMOOTH-A3): REJECT for C1

L1 (full-poly invariance of normalized pilot log-volume) is plausible but has a source gap: every full poly-isomorphism must be checked to be one of the natural poly-isomorphisms covered by Prop3.9. L2 ('SHE-to-membership') is **C1 itself**; its step 5 is the semantic interpretation of SHE, not a proof. L3 gives only the upper bound R_possible subset {x<=h}. Thus L1+L2+L3 does not derive C1; L2 is the gap.

### R8. fitw/subquotient AND route: REJECT

The logical relation (q-itw) => (q-itw AND Theta-itw/indets) => (Theta-itw/indets) is a formal rewriting at the level of intertwinings. It does not produce an output data element D0 or a numerical log-volume equality. The AND/subquotient operations are not a surjectivity statement onto the q-pilot value.

## 3. Specific failure modes

1. **Circularity**: R1/R2/R5/R7 assume an output representing Q or an isomorphism L_H≅L_q, then conclude Q is an output value.
2. **Hidden assumption**: 'construction of the input log-volume' is silently upgraded to 'there exists an output with that log-volume'.
3. **Q-pilot input/output confusion**: Q is the log-volume of the fixed input q-pilot; O/D are output data subject to Ind. A full-poly link of prime-strips is not a member of O and does not give a numerical output value.
4. **Log-volume invariance misuse**: full-poly invariance says if an output D is linked to the q-pilot then logVol(D)=Q; it does not prove such a D exists in O. Invariance of a value under an equivalence is not existence of an element with that value.
5. **Closedness/limit misuse**: a limit of possible output values need not be possible; the source gives no exact error/sign.
6. **Normalization misuse**: local exact volumes and determinant comparisons require the same global packet+procession normalization; the routes do not establish this at the object level.

## 4. Is C1 derivable or disprovable?

C1 is **not derivable** from A1-A3 as stated. A1-A3 constrain O and H by a link and an upper bound; C1 is an existence/membership statement not contained in them. A schematic model with O containing only outputs of log-volume below Q and hull h>Q satisfies the abstract A1-A3 interface and violates C1, so there is no formal implication. This does not disprove the source's C1: it shows C1 is an additional source compatibility assertion, exactly the xi-e/xi-f bridge.

With C1 added, the conditional derivation is valid:

    A1 + A2 + A3 + C1 => Q in R_possible subset {x<=h} => Q <= h.   (4.1)

Thus C1 is the exact missing lemma, not a consequence of the three assumptions.

## 5. Accept/reject table

| route | verdict | exact reason |
|---|---|---|
| R1 APT/SHE/IPL direct | REJECT | input/output confusion; existence not implied; circular |
| R2 closed loop/cQ3/cQ4 | REJECT | loop asserted; intertwinings not numerical membership; circular |
| R3 local exact+sum | REJECT | local volume not global possible output; product/weights/Ind missing |
| R4 closure/limit | REJECT | no closedness/continuity/error bound; limit need not be in set |
| R5 determinant line bundle | REJECT | E_H/L_H≅L_q exact normalization unproved |
| R6 APT fixed point | REJECT | no map/fixed-point theorem |
| R7 L1/L2/L3 | REJECT | L1 source gap; L2=C1; L3 upper bound only |
| R8 fitw/subquotient AND | REJECT | formal intertwining logic, not value membership |

## 6. Verdict

All reviewed C1 derivations fail. C1 is not a consequence of A1=Theorem3.11, A2=Prop3.9, A3=Remark3.9.5 as stated; it is an independent source compatibility/existence lemma (xi-e/xi-f). Adding C1 yields Cor3.12 conditionally, but C1 itself remains unproved. No arbitrary epsilon, profile, normalization, or output section is introduced; no mixed/E3; no Lean.

P6_can remains conditional on C1; target_accepted=false.
