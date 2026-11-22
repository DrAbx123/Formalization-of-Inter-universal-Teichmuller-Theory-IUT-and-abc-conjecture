import tmp.sheaf.n8.closure.C6NormalizedTensorHaar
import tmp.sheaf.n8.closure.C7QPilotMassActual
import tmp.sheaf.n8.closure.C7QPilotRegionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull

/-!
# C6 unit-reference normalization

Normalize the raw C6 tensor Haar by the inverse mass of the actual
`arithmeticTupleCanonicalUnitReference` (not the R1 placeholder hull). -/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C6UnitRefNormalized

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
open scoped BigOperators ENNReal

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {V : iota → Type} [∀ i, Fintype (V i)]
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)

abbrev Blk (places : (i : iota) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : iota) → V i) : Type := ArithmeticTensorTupleBlock places tuple

noncomputable def unitRef : Set (Blk places tuple) :=
  arithmeticTupleCanonicalUnitReference places tuple

noncomputable def unitRefMass : ENNReal := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  exact T.mu (unitRef places tuple)

theorem unitRefMass_pos : 0 < unitRefMass places tuple := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  unfold unitRefMass unitRef
  exact (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple T.mu).2.1

theorem unitRefMass_ne_top : unitRefMass places tuple ≠ ⊤ := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  unfold unitRefMass unitRef
  exact (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple T.mu).2.2.ne

/-- Unit-reference normalized measure. -/
noncomputable def c6UnitRefNormalizedData :
    @Measure (Blk places tuple) (rawData places tuple).measurableSpace := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  exact ENNReal.ofReal (unitRefMass places tuple).toReal⁻¹ • T.mu

theorem c6UnitRefNormalizedData_unitRef :
    c6UnitRefNormalizedData places tuple (unitRef places tuple) = 1 := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  have hpos := unitRefMass_pos places tuple
  have hfin := unitRefMass_ne_top places tuple
  set m : ℝ := (unitRefMass places tuple).toReal with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact ENNReal.toReal_pos (unitRefMass_pos places tuple).ne' (unitRefMass_ne_top places tuple)
  have hmne : m ≠ 0 := hmpos.ne'
  have hmto : (ENNReal.ofReal m).toReal = m := ENNReal.toReal_ofReal (le_of_lt hmpos)
  have hμeq : unitRefMass places tuple = ENNReal.ofReal m := by
    rw [hm, ENNReal.ofReal_toReal]
    exact hfin
  unfold c6UnitRefNormalizedData
  rw [Measure.smul_apply, smul_eq_mul]
  change ENNReal.ofReal (unitRefMass places tuple).toReal⁻¹ * unitRefMass places tuple = 1
  rw [hμeq, hmto]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  rw [inv_mul_cancel₀ hmne, ENNReal.ofReal_one]

section PaperOneFactor

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.LocalFieldIntegralUnits

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

/-- Actual one-factor image of the canonical unit reference in the paper block. -/
def unitRefImageTransport (S : SourceInitialThetaData l) : Prop :=
  Set.image (fun y => C7QPilotRegionActual.e S y)
    (unitRef (C7QPilotRegionActual.places S) (C7QPilotRegionActual.tuple S)) =
    (Integers (CommonPrimeCompletion (C7QPilotRegionActual.placeAtPrime S)) : Set _)

/-- Unit-reference normalized q-pilot mass formula. -/
def qPilotUnitRefMassFormula (S : SourceInitialThetaData l) : Prop :=
  (c6UnitRefNormalizedData (C7QPilotRegionActual.places S)
    (C7QPilotRegionActual.tuple S)
    (C7QPilotRegionActual.qPilotRegion S)).toReal =
    ‖C7QPilotRegionActual.q S‖ ^ (C7QPilotMassActual.d S)

end PaperOneFactor

end LeanFormal.IUT.N8Closure.C6UnitRefNormalized

end