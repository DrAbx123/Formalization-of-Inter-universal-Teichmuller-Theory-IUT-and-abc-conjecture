import tmp.sheaf.xif.paper.S2820E37TransitionActual

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2831E37InfinityNotOverlapActual

open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual

variable (K : Type) [Field K]

theorem S2831_tbar_mem_infinityIdeal :
    tbar K ∈ E37InfinityIdeal K := by
  rw [E37InfinityIdeal, RingHom.mem_ker]
  change E37InfinityEval K (Ideal.Quotient.mk (E37ChartYIdeal K)
    (MvPolynomial.X 1)) = 0
  rw [E37InfinityEval, Ideal.Quotient.lift_mk]
  simp [E37InfinityPolynomialEval]

/-- The chart-Y infinity point is not in the image of the chart-Y overlap map. -/
theorem S2831_infinityPoint_not_mem_overlap_range :
    E37InfinityPoint K ∉ Set.range (E37ChartYOverlapMap K) := by
  intro hmem
  obtain ⟨x, hx⟩ := hmem
  have hxcomap : (PrimeSpectrum.comap
      (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K))
      (x : PrimeSpectrum (E37ChartYOverlapRing K)) :
        PrimeSpectrum (E37ChartYRing K)) =
      (E37InfinityPoint K : PrimeSpectrum (E37ChartYRing K)) := by
    change (E37ChartYOverlapMap K x : PrimeSpectrum (E37ChartYRing K)) =
      (E37InfinityPoint K : PrimeSpectrum (E37ChartYRing K))
    simpa [E37ChartYOverlapMap, E37ChartYOverlap, Spec.map_apply] using hx
  have hrange := PrimeSpectrum.localization_away_comap_range
    (E37ChartYOverlapRing K) (tbar K)
  have hxmem : (E37InfinityPoint K : PrimeSpectrum (E37ChartYRing K)) ∈
      (↑(PrimeSpectrum.basicOpen (tbar K)) :
        Set (PrimeSpectrum (E37ChartYRing K))) := by
    rw [← hrange]
    exact ⟨(x : PrimeSpectrum (E37ChartYOverlapRing K)), hxcomap⟩
  have hnot : tbar K ∉ (E37InfinityPoint K).asIdeal :=
    (PrimeSpectrum.mem_basicOpen (tbar K) (E37InfinityPoint K)).mp hxmem
  exact hnot (S2831_tbar_mem_infinityIdeal K)

#check S2831_tbar_mem_infinityIdeal
#check S2831_infinityPoint_not_mem_overlap_range
#print axioms S2831_infinityPoint_not_mem_overlap_range

end LeanFormal.IUT.XiFPaper.S2831E37InfinityNotOverlapActual
end
