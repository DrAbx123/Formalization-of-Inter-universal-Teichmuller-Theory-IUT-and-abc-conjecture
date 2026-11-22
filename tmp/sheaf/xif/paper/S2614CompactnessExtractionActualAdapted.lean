import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.OModuleCompactnessLayer

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2614CompactnessExtractionActualAdapted

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (C : I.SourceOneCircUCompactness v R n)

/-- **Upper log-degree bound on the hull extracted from the `1,circ U`
compactness premise.**  The premise contains the hull in `scaling * O` and
bounds the log-degree on `O`; additivity of the log-degree gives the upper
bound `logDegree scaling + degreeBound` on the hull. -/
theorem hull_logDegree_le_of_sourceOneCircUCompactness
    (x : I.ThetaPilotPoint v)
    (hx : x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) :
    I.sourceLocalLogDegree v x ≤=
      I.sourceLocalLogDegree v C.scaling + C.layer.degreeBound := by
  obtain ⟨y, hy, hxy⟩ :=
    (mem_scaledRegionImage_iff).mp (C.hull_subset_scaledRegionImage hx)
  rw [hxy, I.sourceLocalLogDegree_mul v C.scaling y]
  exact add_le_add le_rfl (C.layer.unitRegion_logDegree_le y hy)

/-- The same upper bound, packaged: from the `1,circ U` compactness premise
one gets an explicit upper log-degree bound on the whole hull. -/
theorem exists_hull_logDegree_upper_of_sourceOneCircUCompactness :
    ∃ B : Real, ∀ x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
        I.sourceLocalLogDegree v x ≤ B :=
  ⟨I.sourceLocalLogDegree v C.scaling + C.layer.degreeBound,
    fun x hx => I.hull_logDegree_le_of_sourceOneCircUCompactness v R n C x hx⟩

/-- **Signed gap 2 pre-object (lower bound form).**  The signed volume needs
a lower bound on the hull log-degree (equivalently an upper bound on
`-log Theta`), not an upper bound.  This is the exact missing field; it is
not a consequence of `SourceOneCircUCompactness`, whose `layer` only provides
an upper log-degree bound. -/
def SignedHullLowerDegreeBound : Prop :=
  ∃ L : Real, ∀ x : I.ThetaPilotPoint v,
    x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
      L ≤ I.sourceLocalLogDegree v x

/-- **Scaling-class boundedness pre-object.**  A bound on the scaling's
log-degree is not a field of `SourceOneCircUCompactness`; it is named here as
the exact missing input for a bounded scaling class. -/
def ScalingClassBounded (B : Real) : Prop :=
  I.sourceLocalLogDegree v C.scaling ≤ B

#print axioms hull_logDegree_le_of_sourceOneCircUCompactness
#print axioms exists_hull_logDegree_upper_of_sourceOneCircUCompactness

end LeanFormal.IUT.XiFPaper.S2614CompactnessExtractionActualAdapted
end
