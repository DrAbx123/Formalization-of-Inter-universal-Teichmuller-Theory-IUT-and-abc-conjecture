/-! # GenEll06Section3StatementsActual — [GenEll] §3 exact statement layer

PAPER: Mochizuki, Arithmetic elliptic curves in general position, Math. J. Okayama
Univ. 52 (2010) 1-28.  Corpus: papers/motizuki_corpus/text/Arithmetic Elliptic
Curves in General Position.txt, §3 lines 738-1199.

PRIOR ART (STEP 0, not re-proved): BD-class tools S3131BDClassCompositionActual /
S3136BDClassChainToolActual; GenEll shapes S3131GenEllPaperInputActual /
S3131GenEllInputDetailedActual / S3131GenEllEquivalenceShapeActual; Serre large-image
source form S1907SerreLargeImageActual (357 lines, GenEll Thm 3.8 per its docstring).

LABEL: exact paper-input statement ledger (data) + provability classification.
No theorem of this file is claimed as proved. -/

namespace LeanFormal.IUT.XiFPaper.GenEll06Section3StatementsActual

structure GenEllStatementRow where
  label : String
  lineRange : String
  content : String
  classification : String

set_option maxRecDepth 10000 in
def genEllSection3Statements : List GenEllStatementRow :=
  [ ⟨"Lemma 3.1", "762-796", "l >= 5 prime: (i) alpha=(1 1;0 1), beta=(1 0;1 1) generate SL2(F_l); (ii) SL2(F_l) has no nontrivial abelian quotients; (iii) H <= GL2(F_l) containing alpha and one non-upper-triangular matrix contains SL2(F_l); (iv) closed J <= GL2(Z_l) whose mod-l image contains alpha and a non-upper-triangular matrix contains SL2(Z_l)", "PROVABLE (finite group theory + Z_l matrices; no deep input; formalizable with Mathlib linear algebra)"⟩,
    ⟨"Lemma 3.2", "895-910", "(i) a G_K-stable one-dimensional F_l-subspace N of M_l(E) either has v_K(q_E) in l*Z or equals F_l(1); (ii) F_l(1) defines finite flat subgroup scheme mu_l <= E, quotient E'; Tate parameter q_{E'} = q_E^l and deg_inf(E') = l*deg_inf(E)", "DEEP (semi-abelian schemes/Tate uniformization input; paper-input)"⟩,
    ⟨"Definition 3.3", "911-913", "the positive integer v_K(q_E) is the local height of E (or E_K)", "DEFINITION (stateable as data)"⟩,
    ⟨"Remark 3.3.1", "915-919", "for potentially multiplicative reduction, define local height by dividing over a finite extension by the ramification index; independent of the choice", "DEFINITION/ELEMENTARY (well-definedness proof is elementary-but-fiddly; formalizable later)"⟩,
    ⟨"Proposition 3.4", "994-1001", "for eps > 0: deg_inf <~ ht_inf <~ 12(1+eps)*ht_Falt <~ (1+eps)*ht_inf on M_ell(Q); in particular for C in R, {[E] in M_ell(Q)<=d : ht_Falt([E]) <= C} is finite", "DEEP (Faltings heights; first <~ immediate from definitions, rest is [Silv2] input; paper-input)"⟩,
    ⟨"Lemma 3.5", "1011-1027", "eps>0, l prime, H_F <= E_F l-cyclic subgroup scheme with l prime to all local heights of bad multiplicative reduction: (1/(12(1+eps)l))*deg_inf(E) <= ht_Falt(E) + 2 log(l) + C for a constant C independent of E,F,H_F,l", "DEEP-ish (uses Prop 3.4 + semi-abelian extension; reduction to paper-input; the degree bookkeeping may be formalizable after Prop 3.4)"⟩,
    ⟨"Lemma 3.6", "1045-1047", "eps>0: exists C0>0 such that for all x,y in R with y >= 1 and x >= C0*y^(1+eps): x >= y*log(x)", "PROVABLE NOW (elementary real analysis; class A)"⟩,
    ⟨"Lemma 3.7", "1052-1072", "compactly bounded K_V, eps>0: exists C>0 and Galois-finite Exc such that for E_L, d=[L:Q], l prime satisfying (a) l >= 100d*(ht_Falt([E_L]) + C*d^eps) with a bad multiplicative prime, or (b) [E_L] in K_V and l prime to local heights: if (a) then l > all local heights; if (b) and [E_L] not in Exc then E_L has a multiplicative prime; if either and E_L admits an l-cyclic subgroup scheme then [E_L] in Exc", "DEEP (uses Prop 3.4, Lemma 3.5/3.6, finiteness Prop 1.4(iv); paper-input with provable skeleton after inputs)"⟩,
    ⟨"Theorem 3.8", "1145-1166", "compactly bounded K_V, eps>0: exists C>0 and Galois-finite Exc such that for E_L over L with [E_L] not in Exc, d=[L:Q], l prime with (a) l >= 23040*100d*(ht_Falt([E_L]) + C*d^eps) and E_L has a prime of potentially multiplicative reduction, or (b) [E_L] in K_V, l prime to local heights of potentially multiplicative reduction and to 2*3*5: the image of Gal(Qbar/L) -> GL2(Z_l) contains SL2(Z_l)", "DEEP (Faltings-height + Serre large-image input; paper-input; source form also in S1907SerreLargeImageActual)"⟩ ]

theorem genEllSection3Statements_length : genEllSection3Statements.length = 9 := by decide

#check genEllSection3Statements
#check genEllSection3Statements_length

end LeanFormal.IUT.XiFPaper.GenEll06Section3StatementsActual