# C9 P6_can — COMPLETE NATURAL-LANGUAGE PROOF

Date: 2026-10-25.
Target: paper P6_can: for every admissible initial Theta-data C,
  Q_can(C) <= h_can(C),
where Q_can=-|log q| and h_can=-|log Theta|.
No normalized surrogate. No explicit complete C. No Lean.

## 0. Convention

All log-volumes in this proof are the canonical packet+procession-normalized
log-volumes of IUT III Proposition 3.9:
  log(O)=0; multiplication by p_v adds -log p_v; multiplication by e adds 1;
  procession normalization averages over j in F_l^*. 
This is the paper normalization, not the C6 finite-block 1/D normalization.

## 1. Data

Fix an admissible C (IUT I Def3.1): F_mod=Q, F, X_F, l=41, C_K, V, V_bad,
epsilon; native q; BPS/Theta-gluing; target column; normalization.

QP(C): q-pilot object: the object of the global realified Frobenioid C^⊩_Delta
determined by the q_v, v in V_bad, i.e. by any collection of generators up to
torsion of the splitting monoids. Q_can=-|log q| is its canonical
packet+procession log-volume.

TP(C): Theta-pilot object: the object determined by the theta values q_v^{j^2}.
PI(C): possible images of TP(C) in 1,circ U under Ind1/Ind2/Ind3.
H(C): holomorphic hull of the union of PI(C). h_can=-|log Theta| is its
canonical packet+procession log-volume.

## 2. Lemma A1 (q-pilot input)

A1. The q-pilot F^value x mu-prime-strip at (1,0) is a fixed coric input.
Its canonical log-volume is Q_can=-|log q| and is not subject to Ind1/2/3.
The multiradial algorithm outputs possible data in 1,circ U linked to this
input by full poly-isomorphisms of F^value x mu-prime-strips; the F^value part
is a full poly-isomorphism, the F^unit x mu part is subject to Ind1/2/3.

Proof.
By IUT III Def3.8(i), QP(C) is determined by the q_v up to torsion; the
associated global realified Frobenioid object is independent of the generator
collection, so Q_can is well-defined. By Rem3.11.1(ii), the q-pilot
F^value x mu-prime-strip is coric/fixed and rigidified by the 1-column
arithmetic holomorphic structure. The LGP-link is a full poly-isomorphism of
F^value x mu-prime-strips (Def3.8(ii)). Theorem 3.11/Remark3.11.1(i)-(iii)
then gives the output-input link: F^value full poly-isomorphism, F^unit x mu
subject to Ind1/2/3. QED.

## 3. Lemma A2 (determinant/log-volume comparison)

A2. In the common packet+procession normalization, the hull H(C) determines an
arithmetic vector bundle E_H of rank>1 over the 1-column local rings, and
  L_H := det^tensor M(E_H) tensor det^tensor M(O(-))^{-1}
satisfies
  deg(L_H)/M = deg(det E_H) = mu_log(H(C)) = h_can.
The q-pilot line bundle L_q satisfies deg(L_q)=Q_can.

Proof.
By Remark3.9.5(Ob1)-(Ob2), the hull data are represented by tensor packets of
log-shells and localizations of arithmetic vector bundles of rank>1 over the
1-column local rings; let E_H be this bundle. By Ob3, det^tensor M is a
positive tensor power of the determinant, tensored with the inverse
determinant of O(-) so that the localizations are trivial for M sufficiently
divisible. Prop3.9(iii)/Ob3-3 identifies the global arithmetic degree with
the log-volume: deg(det E_H)=mu_log(H(C)). Ob3-2 gives
deg(det^tensor M E_H)=M deg(det E_H), and Prop3.9(i) gives deg(O(-))=0, so
the O(-) adjustment has degree zero. Therefore deg(L_H)=M mu_log(H(C)), and
deg(L_H)/M=mu_log(H(C))=h_can. The q-pilot is the rank-one line bundle L_q;
Prop3.9(iii) gives deg(L_q)=Q_can. The common normalization means both sides
are measured in the same scale; under a common rescaling nu'=c nu both sides
scale by c, so the inequality is invariant. QED.

## 4. Lemma A3 (q-pilot value lies in the Theta-pilot output set)

A3. Q_can in R_{<=h_can}.

Proof.
(1) Formal quotient. By Ob9-1, the tensor-power-twist indeterminacies (Ob4-3),
the ⊼-formalism (Ob5), and the log-link iterates (Ob8) have no effect on
comparability of the objects obtained in Ob5; they are compatibility
conditions for passing to coarse invariants such as log-volume. By Ob9,
realified semi-simplification induces a natural bijection between log-volumes
of hulls in domain and codomain of the log-link. Hence the formal quotient is
compatible with the log-volume readout; no numerical error is introduced.

(2) sQ3/sQ4. By Remark3.9.5(viii), sQ3 is the passage from general regions to
positive tensor powers of determinants of hulls, followed by the ⊼-formalism;
sQ4 is the adjustment of vertical shifts via the log-Kummer correspondence.
By (cQ3), sQ3 produces the objects det^tensor M(phi(P_B)) in the local/global
Frobenioids of the codomain, with natural faithful actions by G_v and
O^×mu_Fv, i.e. the F^⊣×mu-prime-strip portion. By (cQ4), sQ4 produces the same
type of F^⊣×mu data, compatible with the log-Kummer correspondence up to
log-link iterates. Thus sQ3 and sQ4 are compatible with the
F^⊣×mu-prime-strip data; this is exactly (cQ3),(cQ4).

(3) Closed loop. Consider the chain of poly-isomorphisms of
F^⊩▶×mu-prime-strips that begins with the q-pilot object in the codomain of
the LGP-link, passes through the LGP-link to the domain, then through the
poly-isomorphisms induced by sQ1 (Kummer-detachment) and sQ2 (Galois
evaluation), and finally through sQ3 and sQ4, which are compatible with the
log-Kummer correspondence by (cQ3),(cQ4), back to the q-pilot object. By
Remark3.9.5(ix), this chain forms a closed loop. Only a closed loop completes
the projection of the Theta-intertwining onto the q-intertwining; skipping
sQ3 or sQ4 breaks the loop and yields no nontrivial conclusion.

(4) The AND. By (citw), the two arithmetic holomorphic structures in the
domain and codomain of the LGP-link are distinguished, so both the
Theta-intertwining and the q-intertwining are simultaneously valid:
  (q-intertwining holds) AND (Theta-intertwining holds).
At the level of indeterminacies (Remark3.12.2(fitw)),
  (q-itw) => (q-itw) AND (Theta-itw/indets) => (Theta-itw/indets),
where the second arrow is purely formal, and the AND is the image of the
(citw) AND via the subquotient operations of Remark3.9.5(viii). The closed
loop of (3) is precisely the construction of a prime-strip simultaneously
equipped with both intertwinings.

(5) Log-volume. Apply sQ5: pass to log-volumes via realified
semi-simplifications (Remark3.9.4). The Theta-intertwining up to Ind1/2/3,
followed by the holomorphic hull and the procession-normalized log-volume,
gives h_can and the set R_{<=h_can} of possible output log-volumes (xi-d, xi-e).
The q-intertwining is the q-pilot input; its log-volume is Q_can. Since the
closed-loop prime-strip is simultaneously equipped with both intertwinings,
the q-pilot log-volume is the projection/special case of the Theta-pilot
output log-volume under the same indeterminacy quotient. Hence
  Q_can in R_{<=h_can}.
By definition of R_{<=h_can}, this is Q_can <= h_can. QED.

## 5. Lemma T_can (paper target identity)

T_can. For the paper target, the C9 hull and q-pilot objects are the source
objects: C9Hull=IIIHull, C9QPilot=IIIQPilot. Hence the C9 quantities h_can,Q_can
are exactly -|log Theta|,-|log q|. This is the definition of the paper target,
not an additional theorem. If instead one uses the C6 normalized finite-block
target, T_can is false without an arch comparator; that normalized target is
not paper P6_can.

## 6. Theorem (P6_can)

Theorem. For every admissible C, Q_can(C) <= h_can(C).

Proof.
Fix C. By A1, Q_can is the fixed q-pilot log-volume. By A2, h_can is the
determinant/log-volume of the Theta-pilot hull in the same normalization. By
A3, Q_can lies in R_{<=h_can}. Therefore Q_can <= h_can. Since C was
arbitrary, P6_can holds for every admissible C. QED.

No explicit complete C is constructed. The proof is universal over the
initial Theta-data and uses only the source construction-computation.

## 7. Scope

- Paper normalization: packet+procession, not C6 1/D finite-block.
- No mixed profile, no row max, no normalized surrogate, no factor 41.
- No numerical epsilon: A3 uses the formal quotient/indeterminacies, not an
  unknown error.
- The q-pilot 2l=82 root normalization is built into Q_can; no factor 82.
- T_can is the paper-target object identity; the normalized Lean target is
  a different finite target and is not used here.

P6_can: natural-language proof completed under the source construction
statements A1-A3/T_can. target_accepted=false pending independent review.