/-! # Mzk1Section2StatementsActual — [Mzk1] §2 exact statements + classification

PAPER: Mochizuki, Noncritical Belyi Maps (corpus:
papers/motizuki_corpus/text/Noncritical Belyi Maps.txt), §2 lines 42-282.

PRIOR ART (STEP 0): S3131Mzk1StatementActual (statement wrapper); no LeanFormal
Belyi-map infrastructure exists (deep search: LeanFormal hits 9, none for Belyi maps),
so the geometric statements are paper-input with provable elementary lemmas.

LABEL: exact paper-input statement ledger (data) + classification. No claims. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section2StatementsActual

structure Mzk1S2StatementRow where
  label : String
  lineRange : String
  content : String
  classification : String

def mzk1Section2Statements : List Mzk1S2StatementRow :=
  [ ⟨"Lemma 2.1", "44-64", "Separating Properties: C>=2, finite S in P^1(Q) with (i) 0,1,inf in S, (ii) exists r in S with 0<r<1, (iii) every alpha in S other than 0,r,1,inf is >1; beta in Q minus S with (iv) beta/alpha >= C for all alpha in S minus {0,inf}. Write r=m/(m+n), f(x)=x^m (x-1)^n. Then (a) f({0,r,1,inf}) subset {0,f(r),inf}; (b) f'(x)=0 implies x in {0,r,1,inf} subset S; (c) f(beta) notin f(S); (d) (f(beta)+f_0)/(f(alpha)+f_0) >= C for all alpha in S minus {inf} with f(alpha)+f_0 != 0, where f_0 = -min_alpha f(alpha).", "PROVABLE NOW (elementary polynomial/calculus inequalities; class A; formalizable with Mathlib polynomial/real analysis)"⟩,
    ⟨"Lemma 2.2", "106-122", "finite S in P^1(Q) with (i) 0,inf in S, (ii) alpha in S minus {0,inf} implies alpha>0; beta in Q minus S with (iii) beta/alpha >= 2 for all alpha in S minus {0,inf}. Then there exists a nonconstant f in Q[x] defining phi : P^1_Q -> P^1_Q with (a) phi(S) subset {0,1,inf}; (b) phi(beta) notin {0,1,inf}; (c) phi unramified over P^1_Q minus {0,1,inf}.", "PROVABLE (induction on |S| using Lemma 2.1; class A after Lemma 2.1)"⟩,
    ⟨"Lemma 2.3", "136-142", "Seperation of Collections: finite S in P^1(C), C>0 real, beta in P^1(C) minus S: there exists lambda in C such that f(x)=1/(x-lambda) satisfies f(beta) != 0,inf; f(alpha) != inf; |f(beta)| >= C|f(alpha)| for all alpha in S; if beta in Q one may take lambda in Q.", "PROVABLE NOW (choose lambda close to beta; elementary; class A)"⟩,
    ⟨"Lemma 2.4", "144-160", "Reduction to the Rational Case: finite S in P^1(Qbar) subset P^1(C), beta in Qbar minus S: there exists nonconstant f in Qbar(x) defining phi with, for some S_phi in P^1(Qbar): (a) phi(S) subset S_phi; (b) phi(beta) in P^1(Qbar) minus S_phi; (c) phi unramified over P^1_Q minus S_phi; moreover if S,beta are defined over a number field F then phi may be taken defined over F.", "PROVABLE WITH EFFORT (induction on reduced degree of S; algebraic-number infrastructure; class A/B boundary)"⟩,
    ⟨"Theorem 2.5", "207-221", "Belyi Maps Noncritical at Prescribed Points: X smooth proper connected curve over Qbar, S,T finite disjoint subsets of X(Qbar): there exists a morphism phi : X -> P^1_Q with (a) phi unramified over P^1_Q minus {0,1,inf}; (b) phi(S) subset {0,1,inf}; (c) phi(T) intersect {0,1,inf} empty; moreover if X,S,T are defined over a number field F then phi may be taken defined over F.", "DEEP (Riemann-Roch/Serre duality + basepoint-free linear system + reduction via Lemmas 2.2-2.4; paper-input; the analytic-geometric core is class B, the reduction skeleton is formalizable)"⟩ ]

theorem mzk1Section2Statements_length : mzk1Section2Statements.length = 5 := by decide

#check mzk1Section2Statements
#check mzk1Section2Statements_length

end LeanFormal.IUT.XiFPaper.Mzk1Section2StatementsActual