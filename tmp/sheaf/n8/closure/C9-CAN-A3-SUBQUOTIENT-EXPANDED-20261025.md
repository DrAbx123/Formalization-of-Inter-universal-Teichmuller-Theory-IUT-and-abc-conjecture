# CANONICAL A3 — CL1-CL3 EXPANDED

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Source: IUT-III.txt SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

Goal: expand the three residual A3 gaps from the closed-loop route.

## 0. A3 statement

A3: Q_can=-|log q| in R_{<=h_can}, h_can=-|log Theta|.

## 1. CL1 — formal quotient indeterminacies

Source: Remark3.9.5(vii)(Ob9-1), lines 8145-8161; (Ob9), 8128-8144.

Ob9-1 lists the formal indeterminacies arising in the passage to comparable
objects:
  (i) tensor-power-twist indeterminacies (Ob4-3);
  (ii) the ⊼-formalism (Ob5);
  (iii) arbitrary iterates of the log-link (Ob8).

Ob9-1 states: these indeterminacies have NO EFFECT on the comparability of
the objects obtained in Ob5. They function solely as compatibility conditions
that must be satisfied when passing to coarse/set-theoretic invariants such as
the log-volume.

Expansion:
CL1.1 The passage to comparable objects via det^tensor M of a suitable hull
      (Ob5) produces objects in the local/global Frobenioids of the codomain
      F^⊩▶×μ-prime-strip.
CL1.2 The three listed operations (Ob4-3), (Ob5), (Ob8) are formal/stack- or
      diagram-theoretic indeterminacies; by Ob9-1 they do not change
      comparability.
CL1.3 Passing to realified semi-simplifications (Ob9) is a quotient operation
      on domain and codomain of the log-link; it induces a natural bijection
      between log-volumes of hulls in domain and codomain.
CL1.4 Therefore the formal indeterminacy quotient acts compatibly with the
      log-volume readout; the log-volume of the Θ-hull and the q-pilot value
      are well-defined on this quotient.

Conclusion CL1: the formal quotient indeterminacies are not an unknown
numerical error; they are compatibility conditions with no effect on
comparability/log-volume. CL1 is expanded as a quotient-compatibility
statement, not an epsilon.

## 2. CL2 — log-Kummer compatibility of sQ3, sQ4

Source: Remark3.9.5(viii), lines 8173-8195; (ix)(cQ3), 8264-8345;
(cQ4), 8346-8366; (Ob7),(Ob8), 7961-8127; (ix), 8383-8431.

sQ3: passing from more general regions to positive tensor powers of
determinants of hulls, then applying the abstract set-theoretic ⊼-formalism
of (v). Source: lines 8183-8186.
sQ4: adjusting the vertical shifts in the output of the multiradial algorithm
by applying the log-Kummer correspondence. Source: lines 8187-8191.

(cQ3) Compatibility of sQ3 with F^⊣×μ-prime-strip data:
  - hulls in H are stabilized by multiplication by elements of O_K;
  - a positive tensor power of the determinant gives objects
    det^tensor M(phi(P_B)) in local/global Frobenioids of the codomain;
  - pull-back morphisms (base-change) give objects with natural faithful
    actions by local Galois groups G_v and units O^×μ_Fv;
  - this is precisely the F^⊣×μ-prime-strip portion of the F^⊩▶×μ-prime-strip;
  - the quotient induced by the ⊼-formalism is the ⊼-category quotient.
Source: lines 8264-8345.

(cQ4) Compatibility of sQ4 with F^⊣×μ-prime-strip data:
  - the vertical-shift adjustment is obtained by applying the log-Kummer
    correspondence;
  - it produces natural actions by local Galois groups G_v and units
    O^×μ_Fv;
  - this is compatible with the F^⊣×μ-prime-strip data, up to arbitrary
    iterates of the log-link (Ob8).
Source: lines 8346-8366.

Expansion:
CL2.1 sQ3 produces the det^tensor M hull objects and their F^⊣×μ-prime-strip
      data (actions of G_v and O^×μ_Fv).
CL2.2 sQ4 adjusts vertical shifts via the log-Kummer correspondence and
      produces the same type of F^⊣×μ-prime-strip data, compatible up to
      log-link iterates.
CL2.3 Therefore the chain of poly-isomorphisms that passes through sQ3/sQ4
      is compatible with the log-Kummer correspondence; this is (cQ3),(cQ4).

Conclusion CL2: sQ3/sQ4 compatibility is exactly the source properties
(cQ3),(cQ4), expanded as determinant/hull action plus log-Kummer vertical
shift. It is not an unspecified approximation.

## 3. CL3 — subquotient AND and closed loop

Source: Remark3.9.5(viii),(ix), lines 8373-8431; (citw), 10913-10943;
(fitw), 10977-11022.

The operations (sQ1) Kummer-detachment, (sQ2) Galois evaluation, (sQ3)
determinant/hull/⊼, (sQ4) log-Kummer vertical shift, (sQ5) log-volume are
(sub)quotient operations. The goal is the projection of the Θ-intertwining
onto the q-intertwining via a relatively simple (sub)quotient.

Closed-loop construction:
  q-pilot codomain -> LGP-link to domain -> (sQ1),(sQ2) polyisomorphisms
  -> (sQ3),(sQ4) compatible with log-Kummer -> back to q-pilot.
Only a closed loop completes the projection; skipping sQ3 or sQ4 breaks the
loop and yields no nontrivial conclusion (lines 8406-8431).

(citw): the two arithmetic holomorphic structures are distinguished, so both
the Θ-intertwining and q-intertwining are simultaneously valid:
  (q-intertwining holds) AND (Θ-intertwining holds).
(fitw): pass to indeterminacies:
  (q-itw) => (q-itw) AND (Θ-itw/indets) => (Θ-itw/indets).
The second arrow is purely formal; the AND is the image of the (citw) AND via
the subquotient operations of Remark3.9.5(viii).

Expansion:
CL3.1 The closed loop through sQ1-sQ4 constructs a prime-strip simultaneously
      equipped with q-intertwining and Θ-intertwining up to Ind1/2/3.
CL3.2 This realizes the AND of (citw) at the level of the subquotient.
CL3.3 sQ5 (log-volume/realified semi-simplification) passes to the coarse
      log-volume invariant, compatible with CL1/CL2.
CL3.4 The q-pilot log-volume Q_can is the projection/special case of the
      Θ-pilot output log-volume h_can under this subquotient.
CL3.5 Hence Q_can in R_{<=h_can}.

Conclusion CL3: the subquotient AND is the closed-loop construction through
sQ1-sQ4, followed by sQ5 log-volume. It is not an unproved set-theoretic map.

## 4. A3 conclusion

CL1 (formal indeterminacy quotient has no effect on comparability/log-volume)
+ CL2 (sQ3/sQ4 log-Kummer compatibility)
+ CL3 (closed-loop subquotient AND)
⇒ the q-pilot log-volume is a possible Θ-pilot output log-volume
⇒ Q_can in R_{<=h_can}
⇒ Q_can <= h_can.

A3 is now expanded at the source-statement level. The only remaining
formalization work is to encode the subquotient/realified-semi-simplification
operations themselves; no numerical epsilon, no normalization change, no
target change.

P6_can: A1+A2 ratio+A3 expanded+T_can => Cor3.12 => P6_can.
P6: OPEN pending T_can and formal encoding of CL1-CL3.
target_accepted=false.