import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

namespace LeanFormal.IUT.XiFPaper.S2663HullLowerUnboundedActual

variable {l : PrimeGeFive} {V : Type} (I : OriginalInput l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

theorem sourceHolomorphicHull_logDegree_unbounded_below
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    forall C : Real, exists x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
        I.sourceLocalLogDegree v x < C := by
  intro C
  obtain ⟨k, hk⟩ := exists_nat_gt
    (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n zeroSignedLabel) - C)
  let a : Real := -((k : Real) + 1)
  have ha : a ≠ 0 := by
    intro hzero
    have hz : (k : Real) + 1 = 0 := neg_eq_zero.mp hzero
    linarith
  have hs : I.constantThetaPilotPoint v R (Multiplicative.ofAdd a) ∈
      I.sourceScalingUnits v :=
    I.constantThetaPilotPoint_mem_sourceScalingUnits v R (a := a) ha hdeg
  have hx : I.sourceThetaPilotPoint v R n zeroSignedLabel ∈
      I.sourceHolomorphicHull v R n :=
    I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n zeroSignedLabel
  refine ⟨I.constantThetaPilotPoint v R (Multiplicative.ofAdd a) *
      I.sourceThetaPilotPoint v R n zeroSignedLabel, ?_, ?_⟩
  · exact I.sourceHolomorphicHull_scaling_mem v R n hs hx
  · rw [I.sourceLocalLogDegree_mul,
      I.sourceLocalLogDegree_constant v R a hdeg]
    have hcard1 : (1 : Real) ≤ (Fintype.card (SourceVolumeIndex l) : Real) := by
      exact_mod_cast Nat.succ_le_of_lt (sourceVolumeIndex_card_pos l)
    have hk' : (k : Real) + 1 >
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n zeroSignedLabel) - C := by
      linarith
    have hle : -((Fintype.card (SourceVolumeIndex l) : Real) * ((k : Real) + 1))
        ≤ -((k : Real) + 1) := by
      nlinarith
    dsimp [a]
    linarith

theorem not_exists_hull_logDegree_lower_bound
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ∃ C : Real, forall x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
        C ≤ I.sourceLocalLogDegree v x := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx, hlt⟩ :=
    sourceHolomorphicHull_logDegree_unbounded_below I v R n hdeg C
  exact not_lt_of_ge (hC x hx) hlt

end LeanFormal.IUT.XiFPaper.S2663HullLowerUnboundedActual
end
