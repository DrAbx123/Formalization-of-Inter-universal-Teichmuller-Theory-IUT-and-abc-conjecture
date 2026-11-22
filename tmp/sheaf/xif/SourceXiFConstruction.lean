import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceContractedSupplyRealization
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Source construction of the xi-f inclusion

This file constructs the xi-f objects at the actual source value layer:

* the q-pilot point is the theta-pilot point at the actual signed label `j=1`;
* its signed log-volume is the actual source local log-degree;
* the Theta-hull signed log-volume is the supremum of the actual source
  local log-degrees over the actual source holomorphic hull;
* xi-f `qPilotLog <= thetaHullLog` follows from the actual hull membership
  of the q-pilot point, without an input inequality.

The only extra hypothesis for finiteness/nonpositivity is the actual
contraction condition on the source hull scaling units; it is kept explicit.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual q-pilot point at the value layer: the theta-pilot point at label 1. -/
def sourceQPilotPoint (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : I.ThetaPilotPoint v :=
  I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l))

/-- The signed q-pilot log-volume: the actual local log-degree of the q-pilot point. -/
def sourceQPilotLogVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Real :=
  I.sourceLocalLogDegree v (I.sourceQPilotPoint v R n)

/-- The actual values of the local log-degree on the source holomorphic hull. -/
def sourceThetaHullLogValueSet (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Set Real :=
  I.sourceLocalLogDegree v '' (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))

/-- The signed Theta-hull log-volume: the supremum of the source log-degrees
over the actual holomorphic hull. -/
def sourceThetaHullLogVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Real :=
  sSup (I.sourceThetaHullLogValueSet v R n)

theorem sourceQPilotPoint_mem_hull (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceQPilotPoint v R n ∈
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n (oneSignedLabel (l := l))

theorem sourceQPilotLogVolume_mem_valueSet (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceQPilotLogVolume v R n ∈ I.sourceThetaHullLogValueSet v R n :=
  ⟨I.sourceQPilotPoint v R n, I.sourceQPilotPoint_mem_hull v R n, rfl⟩

theorem sourceQPilotLogVolume_eq_gauss (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceQPilotLogVolume v R n =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log ((I.theaterAt 0 0).thetaPacket.q) := by
  unfold sourceQPilotLogVolume sourceQPilotPoint
  rw [I.sourceLocalLogDegree_thetaPilotPoint_gauss v R n (oneSignedLabel (l := l)),
    oneSignedLabel_val, gaussExponent_one_toNat, Nat.cast_one, one_mul]

/-- Source xi-f inclusion from actual hull membership, under boundedness of the
hull log-degree values. -/
theorem sourceXiFInclusion_of_bounded (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hBdd : BddAbove (I.sourceThetaHullLogValueSet v R n)) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n := by
  unfold sourceThetaHullLogVolume
  exact le_csSup hBdd (I.sourceQPilotLogVolume_mem_valueSet v R n)

/-- The boundedness follows from the actual contracted-generator condition:
every source hull scaling unit has nonpositive log-degree and q <= 1. -/
theorem sourceThetaHullLogValueSet_bddAbove_of_contracted (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    BddAbove (I.sourceThetaHullLogValueSet v R n) := by
  refine ⟨0, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact I.sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators
    v R n (I.sourceImageLogDegree_nonpos_of_q_le_one v R n hq) hScaling x hx

/-- Source xi-f: the q-pilot log-volume lies in the Theta-hull log-volume ray. -/
theorem sourceXiFInclusion (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n :=
  I.sourceXiFInclusion_of_bounded v R n
    (I.sourceThetaHullLogValueSet_bddAbove_of_contracted v R n hq hScaling)


/-- The q-pilot signed log-volume is nonpositive under the source q-contraction. -/
theorem sourceQPilotLogVolume_nonpos (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1) :
    I.sourceQPilotLogVolume v R n ≤ 0 := by
  rw [I.sourceQPilotLogVolume_eq_gauss v R n]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (Real.log_nonpos (le_of_lt (I.theaterAt 0 0).thetaPacket.q_pos) hq)

/-- The signed Theta-hull log-volume is nonpositive when every hull point has
nonpositive source log-degree. -/
theorem sourceThetaHullLogVolume_nonpos (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hBound : ∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      I.sourceLocalLogDegree v x ≤ 0) :
    I.sourceThetaHullLogVolume v R n ≤ 0 := by
  unfold sourceThetaHullLogVolume
  apply csSup_le
  · exact ⟨I.sourceQPilotLogVolume v R n, I.sourceQPilotLogVolume_mem_valueSet v R n⟩
  · rintro y ⟨x, hx, rfl⟩
    exact hBound x hx

end OriginalInput
end Theorem311Source

end IUT
