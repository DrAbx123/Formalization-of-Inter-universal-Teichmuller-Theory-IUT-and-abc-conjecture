import tmp.sheaf.xif.paper.S3064InfinityIdealSpanActual
import tmp.sheaf.xif.paper.S3062ChartZPreservationProof
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3064InfinityIdealSpanActual
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S3063ChartYNonoverlapActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3065ChartYNonoverlapActual

abbrev K0 := S3062ChartZPreservationProof.K

local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- U_Y minus the overlap is exactly the infinity point.  This closes
S3062ChartYNonoverlapInfinity. -/
theorem S3065_chartYNonoverlap :
    S3062ChartYNonoverlapInfinity := by
  change ∀ y : PrimeSpectrum (E37ChartYRing K0),
    y ∉ Set.range (E37ChartYOverlapMap K0) → y = E37InfinityPoint K0
  intro y hy
  have hbasic : y ∉ (PrimeSpectrum.basicOpen
      (tbar S2844D6F6BaseChangeActual.K) :
      Set (PrimeSpectrum (E37ChartYRing S2844D6F6BaseChangeActual.K))) := by
    rw [← PrimeSpectrum.localization_away_comap_range
      (E37ChartYOverlapRing S2844D6F6BaseChangeActual.K)
      (tbar S2844D6F6BaseChangeActual.K)]
    exact hy
  have ht : tbar K0 ∈ y.asIdeal := by
    by_contra ht
    exact hbasic ((PrimeSpectrum.mem_basicOpen _ y).mpr ht)
  haveI : y.asIdeal.IsPrime := y.isPrime
  have hs : sbar K0 ∈ y.asIdeal :=
    S3063_sbar_mem_of_tbar_mem y.asIdeal ht
  have hspan : Ideal.span ({sbar K0,
      tbar K0} :
      Set (E37ChartYRing S2844D6F6BaseChangeActual.K)) ≤ y.asIdeal := by
    rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hs
    · exact ht
  have hEq : E37InfinityIdeal K0 = Ideal.span ({sbar K0, tbar K0} :
      Set (E37ChartYRing K0)) := by
    exact S3064_span_eq_infinityIdeal.symm
  have hE : E37InfinityIdeal K0 ≤ y.asIdeal := by
    rw [hEq]
    exact hspan
  have heq : E37InfinityIdeal K0 = y.asIdeal :=
    (E37InfinityIdeal_isMaximal S2844D6F6BaseChangeActual.K).eq_of_le
      y.isPrime.ne_top hE
  apply PrimeSpectrum.ext
  change y.asIdeal = E37InfinityIdeal K0
  exact heq.symm

/-- Point realization outside infinity, actual from S3065 plus the transition
overlap preimage. -/
theorem S3065_pointRealization
    (hover : S3062ChartYOverlapPreimage) : S3062PointRealization :=
  S3062_pointRealization_of_glue S3065_chartYNonoverlap hover

#check S3065_chartYNonoverlap
#check S3065_pointRealization
#print axioms S3065_chartYNonoverlap
#print axioms S3065_pointRealization

end LeanFormal.IUT.XiFPaper.S3065ChartYNonoverlapActual
end
