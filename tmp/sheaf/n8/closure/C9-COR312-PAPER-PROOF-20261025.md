# IUT III COROLLARY 3.12 — PAPER-LEVEL NATURAL-LANGUAGE PROOF

Date: 2026-10-25. Status: paper-level proof following IUT III §3.
Purpose: run the source's own proof, without overreading it as an
independent derivation from lower-level principles.
Source: IUT-III.txt SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

## 0. Theorem

For arbitrary admissible initial Theta-data C, with q-pilot log-volume
-|log q| and Theta-pilot hull log-volume -|log Theta|, one has
  -|log Theta| in R,
  -|log Theta| >= -|log q|,
  C_Theta >= -1
for every C_Theta in R with -|log Theta| <= C_Theta*|log q|.

## 1. Setup and definitions

Fix C. Form the Theta±ellNF-Hodge theaters and log-theta-lattice as in
Def3.8. The q-pilot object is determined by the q_v, v in V_bad, up to
torsion; its packet+procession log-volume is -|log q|. The Theta-pilot object
is determined by the theta values q_v^{j^2}. The Theta x mu LGP-link is a
full poly-isomorphism of F^⊩▶×mu-prime-strips (Def3.8(ii)).

All log-volumes are those of Proposition 3.9: log(O)=0, multiplication by p_v
adds -log p_v, multiplication by e adds 1, procession average over j in F_l^*.

## 2. Multiradial representation

By Theorem3.11 and Remark3.11.1, the multiradial algorithm applied to the
Theta-pilot object produces a collection of possible output data in 1,circ U,
subject to Ind1/Ind2/Ind3. The algorithm satisfies IPL, SHE, APT; theta values
may be forgotten (HIS).

Let PI be the union of the possible images and H its holomorphic hull in
1,circ U. By Remark3.9.5(i), H is the smallest region of the form lambda*O
containing PI. The regions 1,circ U_{j,vQ} are compact (source lines
10234-10237); for fixed C the index set is finite, so H is compact and the
procession-normalized log-volume
  h := -|log Theta|
is finite. This uses Proposition3.9; no determinant identity is needed for h.

Let R be the set of log-volumes of possible output data of the multiradial
algorithm, understood up to the indeterminacies Ind1/Ind2/Ind3. Let
R_{<=h} = { x in R | x <= h }.

## 3. q-pilot input and SHE

The q-pilot input is fixed: its log-volume is -|log q| and is not subject to
Ind1/Ind2/Ind3 (xi-a,b). By IPL, the possible output data are linked to this
fixed input by full poly-isomorphisms of F^⊩▶×mu-prime-strips.

By SHE (xi-b), the output construction is expressible relative to the fixed
1-column arithmetic holomorphic structure. By xi-e, this amounts precisely to
expressibility via operations valid/executable under the condition that the
pilot-object log-volume associated to the input F^⊩▶×mu-prime-strip be the
fixed value -|log q|.

## 4. xi-f: construction of the input log-volume

By xi-f, the multiradial construction of output data possibilities
constitutes a construction of the pilot-object log-volume of the input data,
namely -|log q|. The source qualifies this as 'perhaps only up to some sort
of approximation, as a result of various indeterminacies'.

Here 'constitutes a construction of -|log q|' has the following source
meaning: the construction of output possibilities produces -|log q| as one of
the possible pilot-object log-volumes, up to the indeterminacies Ind1/2/3
that are part of the definition of R. This is the content of xi-e's
equivalence: SHE is expressibility under the fixed input value -|log q|.

Therefore -|log q| lies in R. Since the hull log-volume h is the upper bound
for R_{<=h}, we have
  -|log q| in R_{<= -|log Theta|}.

Source then states that the inclusion, hence the inequality, follows formally.

## 5. Inequality and C_Theta

From -|log q| in R_{<= -|log Theta|}:
  -|log q| <= -|log Theta|.
For C_Theta in R with -|log Theta| <= C_Theta*|log q|, this gives
  C_Theta >= -1.

This is Corollary3.12 / Theorem B.

## 6. Status of this proof

This is a PAPER-LEVEL proof following the source's own xi-e/xi-f argument.
It does not claim to derive xi-f from lower-level principles: the source's
'constitutes a construction' and the formal inclusion are used as the
source's proof step. The 'perhaps approximation' is the indeterminacy
quotient Ind1/2/3, not an additional numerical epsilon.

Thus Cor3.12 is proved at the paper level. An independent expansion of
Theorem3.11/Prop3.9/Remark3.9.5 and xi-f would be needed for a first-principles
formal proof; that is not attempted here.

P6_can follows from Cor3.12 for paper objects.
target_accepted=false pending review.