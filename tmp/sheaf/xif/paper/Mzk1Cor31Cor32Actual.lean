/-! # Mzk1Cor31Cor32Actual — [Mzk1] Cor 3.1/3.2 statements + reductions from Thm 2.5

STEP 0 prior-art: corpus papers/motizuki_corpus/text/Noncritical Belyi Maps.txt
Cor 3.1 lines 283-296 (+ proof 297-319), Cor 3.2 lines 323-345 (+ proof 346-398).
Thm 2.5 statement layer: Mzk1Theorem25StatementActual; elementary lemmas:
Mzk1Lemma21Actual (Lemma 2.1 (b) core), Mzk1Lemma22/23/24 planned.

LABEL: exact paper-input statement ledger + reduction classification (data).
No corollary is claimed as proved. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor31Cor32Actual

structure Mzk1CorStatementRow where
  label : String
  lineRange : String
  content : String
  reductionFromThm25 : String
  classification : String

def mzk1CorStatements : List Mzk1CorStatementRow :=
  [ ⟨"Corollary 3.1", "283-296", "n>=1 integer, X smooth proper connected over Qbar, S finite subset X(Qbar): exists finite collection phi_1..phi_N : X -> P^1_Q such that (a) each phi_i unramified over P^1_Q minus {0,1,inf}; (b) phi_i(S) subset {0,1,inf}; (c) for any T subset X(Qbar) of cardinality n with S intersect T empty, there exists i with phi_i(T) intersect {0,1,inf} empty.", "proof p.297-319: view T as Q-valued point of Y=(X minus S)^n; sets U_phi = {y : phi(y) disjoint from {0,1,inf}} are nonempty open (Theorem 2.5); they cover Y(Qbar); Y quasi-compact => finitely many cover => N.", "C-REDUCTION (given Thm 2.5 + quasi-compactness of the n-fold product and Zariski openness; formalizable after Thm 2.5 statement/reduction)"⟩,
    ⟨"Corollary 3.2", "323-345", "c,d>=1, X smooth proper connected over number field F subset Qbar, V finite set of valuations: exists finite collection phi_1..phi_N : X -> P^1_Q and, for each v in V, a locally compact field L_v with F subset F_v subset L_v containing all Q-conjugates of extensions of F of degree <= d, and compact H_v subset (P^1 minus {0,1,inf})(L_v), such that (iii) every phi_i defined over every L_v; (iv) phi_i unramified over P^1_Q minus {0,1,inf}; (v) for any T subset X(Qbar) of cardinality <= c of points with field of definition of degree <= d over F, exists i with phi_i(x^sigma) in H_v for all x in T, sigma in Gal(Qbar/F), v in V.", "proof p.346-398: n=c*d; Y=X^n; L_v locally compact containing F_v and all conjugates; U_phi subsets of product prod Y(L_v) are nonempty open relative to product Zariski topologies (Theorem 2.5 + local compactness); cover argument yields finite collection.", "C-REDUCTION (given Thm 2.5 + local compactness/product topologies; class B only via Thm 2.5)"⟩ ]

theorem mzk1CorStatements_length : mzk1CorStatements.length = 2 := rfl

/-- Ordered reduction plan for the corollaries (data). -/
def mzk1CorReductionPlan : List (String × String) :=
  [ ("input", "Theorem 2.5 (Mzk1Theorem25StatementActual / GeometricCore + Lemmas 2.2/2.3/2.4)"),
    ("Cor 3.1 step 1", "Y = (X minus S)^n is a Q-variety; T of cardinality n corresponds to a Q-valued point of Y"),
    ("Cor 3.1 step 2", "for each admissible phi, U_phi subset Y(Qbar) is nonempty open (Theorem 2.5 applied to T, S)"),
    ("Cor 3.1 step 3", "{U_phi} covers Y(Qbar); Y quasi-compact => finite subcover => N"),
    ("Cor 3.2 step 1", "Y = X^n with n=c*d; T's conjugates form a point of prod_v Y(L_v)"),
    ("Cor 3.2 step 2", "U_phi subsets of prod Y(L_v) are open for product of Zariski topologies, hence open for product of L_v-topologies"),
    ("Cor 3.2 step 3", "compactness of prod H_v-type regions + finite subcover argument gives phi_1..phi_N, H_v") ]

theorem mzk1CorReductionPlan_length : mzk1CorReductionPlan.length = 7 := rfl

#check mzk1CorStatements_length
#check mzk1CorReductionPlan_length

end LeanFormal.IUT.XiFPaper.Mzk1Cor31Cor32Actual