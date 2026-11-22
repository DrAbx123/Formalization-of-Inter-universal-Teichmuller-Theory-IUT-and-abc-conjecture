import tmp.sheaf.xif.paper.S3062ChartZPreservationProof
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3063ChartYNonoverlapActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev R1 := E37ChartYRing S2844D6F6BaseChangeActual.K

/-- span{sbar,tbar} is contained in the infinity ideal, actual. -/
theorem S3063_span_le_infinityIdeal :
    Ideal.span ({sbar S2844D6F6BaseChangeActual.K,
      tbar S2844D6F6BaseChangeActual.K} : Set R1) ≤
      E37InfinityIdeal S2844D6F6BaseChangeActual.K := by
  rw [Ideal.span_le]
  intro z hz
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · apply RingHom.mem_ker.mpr
    change E37InfinityEval S2844D6F6BaseChangeActual.K
      (Ideal.Quotient.mk (E37ChartYIdeal S2844D6F6BaseChangeActual.K)
        (MvPolynomial.X 0)) = 0
    rw [E37InfinityEval, Ideal.Quotient.lift_mk]
    simp [E37InfinityPolynomialEval]
    rfl
  · apply RingHom.mem_ker.mpr
    change E37InfinityEval S2844D6F6BaseChangeActual.K
      (Ideal.Quotient.mk (E37ChartYIdeal S2844D6F6BaseChangeActual.K)
        (MvPolynomial.X 1)) = 0
    rw [E37InfinityEval, Ideal.Quotient.lift_mk]
    simp [E37InfinityPolynomialEval]
    rfl

/-- In a prime containing tbar, the chart-Y relation forces sbar into the prime. -/
theorem S3063_sbar_mem_of_tbar_mem
    (p : Ideal R1) [p.IsPrime]
    (hp : tbar S2844D6F6BaseChangeActual.K ∈ p) :
    sbar S2844D6F6BaseChangeActual.K ∈ p := by
  have hrel : sbar S2844D6F6BaseChangeActual.K ^ 3 -
      sbar S2844D6F6BaseChangeActual.K * tbar S2844D6F6BaseChangeActual.K ^ 2 -
      tbar S2844D6F6BaseChangeActual.K -
      tbar S2844D6F6BaseChangeActual.K ^ 2 = 0 := by
    have h := chartYRelation_quotient S2844D6F6BaseChangeActual.K
    simpa [sbar, tbar, E37ChartYPolynomial, map_sub, map_mul, map_pow] using h
  have ht2 : tbar S2844D6F6BaseChangeActual.K ^ 2 ∈ p := by
    simpa [pow_two] using p.mul_mem_left (tbar S2844D6F6BaseChangeActual.K) hp
  have hst2 : sbar S2844D6F6BaseChangeActual.K * tbar S2844D6F6BaseChangeActual.K ^ 2 ∈ p :=
    p.mul_mem_left (sbar S2844D6F6BaseChangeActual.K) ht2
  have hmem : sbar S2844D6F6BaseChangeActual.K ^ 3 ∈ p := by
    rw [show sbar S2844D6F6BaseChangeActual.K ^ 3 =
        sbar S2844D6F6BaseChangeActual.K * tbar S2844D6F6BaseChangeActual.K ^ 2 +
        tbar S2844D6F6BaseChangeActual.K +
        tbar S2844D6F6BaseChangeActual.K ^ 2 from by linear_combination hrel]
    exact p.add_mem (p.add_mem hst2 hp) ht2
  exact (inferInstance : p.IsPrime).mem_of_pow_mem 3 hmem

/-- Exact missing ideal equality: E37InfinityIdeal = span{sbar,tbar}. -/
def S3063InfinityIdealSpan : Prop :=
  E37InfinityIdeal S2844D6F6BaseChangeActual.K ≤
    Ideal.span ({sbar S2844D6F6BaseChangeActual.K,
      tbar S2844D6F6BaseChangeActual.K} : Set R1)

/-!
## Exact lemmas and first error

Actual:
* S3063_span_le_infinityIdeal: span{sbar,tbar} ≤ E37InfinityIdeal;
* S3063_sbar_mem_of_tbar_mem: in a prime containing tbar, sbar is in the prime
  (from sbar^3 = sbar tbar^2 + tbar + tbar^2).

Missing (S3063InfinityIdealSpan): the reverse ideal inclusion
E37InfinityIdeal ≤ span{sbar,tbar}.  Route: E37InfinityEval is evaluation at
(s,t)=(0,0); kernel on K[s,t] is (s,t), and its image in R1 is span{sbar,tbar};
equivalently quotient by span{sbar,tbar} is K.  Not formalized.

Given S3063InfinityIdealSpan, the nonoverlap lemma follows:
y ∉ range(overlap) => tbar ∈ y.asIdeal; then sbar ∈ y.asIdeal; hence
E37InfinityIdeal ≤ span{sbar,tbar} ≤ y.asIdeal; maximality gives y = ∞.

Second missing piece remains S3062ChartYOverlapPreimage (transition/open
immersion).  No ideal equality or nonoverlap is faked.
-/

#check S3063_span_le_infinityIdeal
#check S3063_sbar_mem_of_tbar_mem
#check S3063InfinityIdealSpan
#print axioms S3063_span_le_infinityIdeal
#print axioms S3063_sbar_mem_of_tbar_mem

end LeanFormal.IUT.XiFPaper.S3063ChartYNonoverlapActual
end
