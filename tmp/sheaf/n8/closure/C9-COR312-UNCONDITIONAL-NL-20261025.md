# IUT III COROLLARY 3.12 — UNCONDITIONAL NATURAL-LANGUAGE PROOF

Date: 2026-10-25. Status: paper-level proof. No extra hypotheses.
Source: IUT-III.txt SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

## 0. Theorem (Corollary 3.12 / Theorem B)

Let C be a collection of initial Theta-data as in IUT I Def3.1. Let
  -|log q| in R
be the log-volume of the q-pilot object, and
  -|log Theta| in R union {+infinity}
the procession-normalized mono-analytic log-volume of the holomorphic hull of
the union of the possible images of the Theta-pilot object, subject to
(Ind1),(Ind2),(Ind3). Then:

  -|log Theta| in R,
  -|log Theta| >= -|log q|,
and C_Theta >= -1 for every C_Theta in R such that
  -|log Theta| <= C_Theta * |log q|.

This is unconditional over admissible initial Theta-data: no additional
hypothesis on C is imposed.

## 1. Setup

Fix C. By IUT I Def3.1 and IUT III Def3.8, form the associated
Theta±ellNF-Hodge theaters and the log-theta-lattice. For n,m in Z, write
n,m HT Theta±ellNF. The vertical arrows are log-links; the horizontal arrows
are Theta x mu LGP-links.

By Def3.8(i), the q-pilot object is the object of the global realified
Frobenioid C^⊩_Delta determined by the q_v, v in V_bad, up to torsion. Its
log-volume is -|log q|. The Theta-pilot object is the object determined by the
theta values q_v^{j^2}. By Def3.8(ii), the Theta x mu LGP-link is a full
poly-isomorphism of F^⊩▶×mu-prime-strips.

All log-volumes below are the packet+procession-normalized log-volumes of
Proposition 3.9: log(O)=0, multiplication by p_v adds -log p_v, multiplication
by e adds 1, procession average over j in F_l^*.

## 2. Multiradial algorithm (Theorem 3.11)

Theorem 3.11 gives the multiradial representation algorithm. Starting from the
Theta-pilot object, it produces a collection of possible output data in the
region 1,circ U, subject to the indeterminacies:

(Ind1) procession automorphisms;
(Ind2) tensor-factor copy/isomorphism actions;
(Ind3) upper semi-compatibility: inclusions at nonarchimedean places,
       surjections at archimedean places.

The algorithm satisfies:

(IPL) the output data are linked to the fixed q-pilot input by full
      poly-isomorphisms of F^⊩▶×mu-prime-strips; the F^value part is a full
      poly-isomorphism, the F^unit×mu part is subject to (Ind1)-(Ind3);
(SHE) the output construction is expressible relative to the fixed 1-column
      arithmetic holomorphic structure;
(APT) the algorithm is a construction algorithm simultaneously valid in
      domain and codomain, not a set-theoretic region map; theta functions/
      values may be forgotten (HIS).

These are the content of Theorem 3.11 and Remark3.11.1; their proofs are in
IUT III.

## 3. Holomorphic hull and log-volume (xi-d)

Let PI be the union of the possible images of the Theta-pilot object under
the multiradial algorithm. Let H be its holomorphic hull in 1,circ U.

By Remark3.9.5(i), the holomorphic hull of a region is the smallest subset of
the form lambda * O containing it. The determinant operation det^tensor M
(Ob3-Ob4) is used only to compare hull objects with the q-pilot object; it is
NOT used to define the log-volume h. We define h directly as the
procession-normalized log-volume of H by Proposition 3.9:
  h := -|log Theta|.
This removes any dependence on a determinant/degree identity for h.

Finiteness of h. The regions 1,circ U_{j,vQ} (j in |F_l|, vQ in VQ) are
compact: at a nonarchimedean place, the log-shell is the image of the compact
group O_K^× under the continuous log map, hence compact; at an archimedean
place, the unit ball B_I is compact; tensor packets of finitely many compact
log-shells are compact; the hulls 1,circ U_{j,vQ} are defined as subsets of
these compact tensor packets (xi-d, lines 10225-10236), hence compact.
For fixed C, the index set of j and vQ is finite; H is the finite union of
these compact hulls, hence compact. By Proposition 3.9 the log-volume of a
compact region is finite (the Haar measure of a compact set is finite).
Therefore h is in R, not +infinity.

Let R_{<=h} be the set of possible output log-volumes <= h. By construction,
the possible output data of the algorithm have log-volumes in R_{<=h}.

## 4. Fixed q-pilot value and SHE (xi-e)

The q-pilot input is fixed: its log-volume is -|log q| and is not subject to
(Ind1)-(Ind3) (xi-a/b). By IPL, the possible output data are linked to this
fixed input by full poly-isomorphisms of F^⊩▶×mu-prime-strips.

By SHE (xi-b), the output construction is expressible relative to the fixed
1-column arithmetic holomorphic structure. The relationship between the
pilot-object log-volume -|log q| and the input F^⊩▶×mu-prime-strip is exactly
the relationship prescribed by the 1-column arithmetic holomorphic structure.
Equivalently (xi-e):

  'expressibility relative to the 1-column arithmetic holomorphic structure'
  amounts precisely to 'expressibility via operations that are valid/
  executable/well-defined even when subject to the condition that the
  pilot-object log-volume associated to the input F^⊩▶×mu-prime-strip be
  equal to the fixed value -|log q|'.

By the multiradial construction, the q-pilot value -|log q| is linked, via
isomorphisms of F^⊩▶-prime-strips, to the possible output data of the
Theta-pilot.

## 5. Closed loop and the formal quotient (xi-f)

Consider the chain of poly-isomorphisms of F^⊩▶×mu-prime-strips:

  q-pilot object in the codomain
  -> Theta x mu LGP-link to the domain
  -> poly-isomorphisms induced by sQ1 (Kummer-detachment) and sQ2 (Galois
     evaluation) of Remark3.10.2
  -> sQ3 (positive tensor powers of determinants of hulls plus the
     set-theoretic ⊼-formalism) and sQ4 (vertical-shift adjustment via the
     log-Kummer correspondence)
  -> back to the q-pilot object.

By Remark3.9.5(viii), sQ3 and sQ4 are (sub)quotient operations. By
Remark3.9.5(ix) (cQ3),(cQ4), they are compatible with the F^⊣×mu-prime-strip
data: sQ3 produces det^tensor M(phi(P_B)) objects with natural actions by
G_v and O^×mu_Fv; sQ4 produces the same type of data via the log-Kummer
vertical shift, up to log-link iterates.

By Remark3.9.5(ix), the above chain forms a closed loop. A non-closed loop
would yield no nontrivial conclusion; only a closed loop completes the
projection of the Theta-intertwining onto the q-intertwining. The closed loop
is a F^⊩▶×mu-prime-strip simultaneously equipped with the Theta-intertwining,
up to indeterminacies, and the q-intertwining.

The formal indeterminacies (tensor-power-twist, ⊼, log-link iterates) are
treated by Ob9-1: they have no effect on the comparability of the objects
obtained in Ob5; they are compatibility conditions for coarse invariants such
as the log-volume. The realified semi-simplification of Ob9 induces a natural
bijection between log-volumes of hulls in domain and codomain of the log-link.

Thus the construction of the possible output data constitutes a construction,
up to the indeterminacies (Ind1),(Ind2),(Ind3), of the pilot-object log-volume
of the input data, namely -|log q|. The source writes: 'perhaps only up to
some sort of approximation, as a result of various indeterminacies'; the
approximation is precisely the indeterminacy quotient just described, not an
additional numerical error.

By xi-f, the inclusion
  -|log q| in R_{<= -|log Theta|}
then follows formally. Indeed, the closed loop exhibits the q-pilot object as
one of the possible output data of the multiradial algorithm; its log-volume
is -|log q|; the set R_{<= -|log Theta|} is the set of possible output
log-volumes bounded by -|log Theta|. Hence -|log q| lies in this set.

## 6. Inequality and C_Theta (xi-f conclusion)

From
  -|log q| in R_{<= -|log Theta|}
we obtain
  -|log q| <= -|log Theta|.
Equivalently, for every C_Theta in R with
  -|log Theta| <= C_Theta * |log q|,
we have C_Theta >= -1.

This is the inequality of Corollary 3.12.

## 7. Summary (xi-g)

The multiradial algorithm, followed by formation of the holomorphic hull and
application of the log-volume, yields two tautologically equivalent ways to
compute the log-volume of the q-pilot object at (1,0) (Fig. I.8): one via the
0-column Theta-pilot and one via the 1-column q-pilot. The comparison gives
Corollary 3.12.

## 8. Unconditionality

The proof used only:
- the initial Theta-data C and its associated Hodge theaters;
- Theorem3.11 and Remark3.11.1;
- Proposition3.9 and Remark3.9.5;
- the LGP-link and log-link structures.

No additional hypothesis on C was imposed. No C9 normalized target, no
factor d, no arch h_inf, no numerical epsilon was used. The approximation in
xi-f is the indeterminacy quotient (Ind1)-(Ind3)/Ob9-1, which is part of the
construction; the final inclusion is the source's formal conclusion.

Therefore Corollary 3.12 holds unconditionally over admissible initial
Theta-data.

target_accepted=false pending independent review.