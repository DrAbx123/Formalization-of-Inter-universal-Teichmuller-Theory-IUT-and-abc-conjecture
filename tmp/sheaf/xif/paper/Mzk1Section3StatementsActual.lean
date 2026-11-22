/-! # Mzk1Section3StatementsActual — [Mzk1] §3 exact statements + classification

PAPER: Mochizuki, Noncritical Belyi Maps (corpus:
papers/motizuki_corpus/text/Noncritical Belyi Maps.txt), §3 lines 282-398.

PRIOR ART (STEP 0): S3131Mzk1StatementActual; no LeanFormal Belyi infrastructure
(hence paper-input statements; Cor 3.1/3.2 are consequences of Theorem 2.5 +
Zariski quasi-compactness/topology arguments).

LABEL: exact paper-input statement ledger (data) + classification. No claims. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section3StatementsActual

structure Mzk1S3StatementRow where
  label : String
  lineRange : String
  content : String
  classification : String

def mzk1Section3Statements : List Mzk1S3StatementRow :=
  [ ⟨"Corollary 3.1", "283-296", "Belyi Maps Noncritical at Arbitrary Sets of Prescribed Cardinality: n>=1, X smooth proper connected over Qbar, S finite subset X(Qbar): there exists a finite collection phi_1..phi_N : X -> P^1_Q such that (a) each phi_i unramified over P^1_Q minus {0,1,inf}; (b) phi_i(S) subset {0,1,inf} for all i; (c) for any T subset X(Qbar) of cardinality n with S intersect T empty, there exists i with phi_i(T) intersect {0,1,inf} empty.", "DEEP CONSEQUENCE of Theorem 2.5 (covering argument on the n-fold product; class B given Thm 2.5)"⟩,
    ⟨"Corollary 3.2", "323-345", "Belyi Maps Noncritical Near Arbitrary Points of Prescribed Degree: c,d>=1, X smooth proper connected over number field F subset Qbar, V finite set of valuations: there exist finite collection phi_1..phi_N : X -> P^1_Q and, for each v in V, a locally compact field L_v and compact H_v subset (P^1 minus {0,1,inf})(L_v) such that (i) F subset F_v subset L_v; (ii) L_v contains all Q-conjugates of all extensions of F of degree <= d; (iii) every phi_i is defined over every L_v; (iv) phi_i unramified over P^1_Q minus {0,1,inf}; (v) for any T subset X(Qbar) of cardinality <= c of points with field of definition of degree <= d over F, there exists i such that phi_i(x^sigma) in H_v for all x in T, sigma in Gal(Qbar/F), v in V.", "DEEP (product/LV-topology covering + Thm 2.5; class B paper-input)"⟩ ]

theorem mzk1Section3Statements_length : mzk1Section3Statements.length = 2 := rfl

#check mzk1Section3Statements_length

end LeanFormal.IUT.XiFPaper.Mzk1Section3StatementsActual