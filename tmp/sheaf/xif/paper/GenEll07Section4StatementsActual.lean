/-! # GenEll07Section4StatementsActual — [GenEll] §4 exact statement layer (GRH condition named)

PAPER: Mochizuki, Arithmetic elliptic curves in general position, Math. J. Okayama
Univ. 52 (2010) 1-28.  Corpus: Arithmetic Elliptic Curves in General Position.txt,
§4 lines 1200-1425.

PRIOR ART (STEP 0): Lemma 4.2 elementary estimates; Lemma 4.1 is the analytic input
(prime existence of prescribed size; GRH-conditional in the sense of Remark 4.1.1);
Cor 4.3/4.4 use Theorem 3.8 (see GenEll06Section3StatementsActual).

LABEL: exact paper-input statement ledger (data) + classification. No claims. -/

namespace LeanFormal.IUT.XiFPaper.GenEll07Section4StatementsActual

structure GenEllS4StatementRow where
  label : String
  lineRange : String
  content : String
  classification : String

set_option maxRecDepth 10000 in
def genEllSection4Statements : List GenEllS4StatementRow :=
  [ ⟨"Lemma 4.1", "1208-1240", "notation theta(x)=sum_{p<=x} log p, x_A=sum_{p in A} log p; let M positive, eps,x_eps,C_eps>0 with 0<eps<1/4, eps*x_eps>C_eps, and (i) (5/4)x+C_eps >= theta(x) for all x, theta(x) > (1-eps)x for x >= x_eps; (ii) M log x <= eps x for x >= x_eps. Then for any h>=0 and finite set of primes A with x_A > x_eps there exist M distinct primes p_1..p_M with p_j notin A and h <= p_j <= (1+6eps)x_A + 8h.", "CONDITIONAL ANALYTIC (class B: inputs are PNT-type bounds (i),(ii); proof given via theta estimates; formalizable once theta/PNT bounds are supplied; GRH enters only in producing (eps,x_eps,C_eps) per Remark 4.1.1)"⟩,
    ⟨"Remark 4.1.1", "1262-1266", "finding eps,x_eps,C_eps satisfying Lemma 4.1(ii) is elementary; condition (i) is the PNT-type input (the original paper discusses GRH-conditional prime existence in this circle of ideas)", "NOTE (class-B input naming)"⟩,
    ⟨"Lemma 4.2", "1266-1279", "n>=1, primes p_j, positive integers h_j: sum log p_j <= h; sum log(h_j) <= sum log(h_j+1) <= (3/2)h, where h = sum h_j log p_j", "PROVABLE NOW (elementary inequalities; class A)"⟩,
    ⟨"Corollary 4.3", "1282-1314", "eps>0: exists C>0 and Galois-finite Exc such that for E_L over L (L minimal field of definition, [E_L] notin Exc) with a prime of potentially multiplicative reduction, S finite set of primes, d=[L:Q], x_S=sum_{p in S} log p: there exist primes l_0,l_1 notin S with (a) prime to potentially multiplicative primes, local heights; l_1 prime to ramified primes and ramification indices; (b) image of Gal(Qbar/L)->GL2(Z_{l_0}) contains SL2(Z_{l_0}) and Gal->GL2(Z_{l_1}) is surjective; (c) l_0 <= 23040*900d*ht_Falt([E_L])+2x_S+C*d^(1+eps), l_1 <= 23040*900d*ht_Falt([E_L])+6d*log-diff_{M_ell}([E_L])+2x_S+C*d^(1+eps)", "DEEP-REDUCTION (uses Theorem 3.8(a) + Lemma 4.1/4.2 + Prop 3.4; paper-input; proof skeleton is formalizable after Thm 3.8/Prop 3.4/Lemma 4.1 inputs)"⟩,
    ⟨"Corollary 4.4", "1358-1390", "compactly bounded K_V: exists C>0 and Galois-finite Exc such that for E_L over L (L minimal, [E_L] in K_V, notin Exc), S finite, d=[L:Q], x_S as above: there exist primes l_0,l_1 notin S with (a) prime to potentially multiplicative primes, local heights (and l_1 prime to ramified primes and ramification indices); (b) image of Gal(Z_{l_0}) contains SL2(Z_{l_0}) and Gal->GL2(Z_{l_1}) is surjective; (c) inequalities l_0 <= 23040*100d*ht_Falt([E_L])+2x_S+C*d, l_1 <= 23040*100d*ht_Falt([E_L])+6d*log-diff_{M_ell}([E_L])+2x_S+C*d", "DEEP-REDUCTION (uses Theorem 3.8(b) + Lemma 4.1/4.2; paper-input; GRH-conditional only via Lemma 4.1 constants)"⟩ ]

theorem genEllSection4Statements_length : genEllSection4Statements.length = 5 := by decide

#check genEllSection4Statements
#check genEllSection4Statements_length

end LeanFormal.IUT.XiFPaper.GenEll07Section4StatementsActual