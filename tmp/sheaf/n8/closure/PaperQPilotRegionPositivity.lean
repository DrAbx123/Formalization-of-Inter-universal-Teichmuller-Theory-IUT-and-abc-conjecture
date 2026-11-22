import tmp.sheaf.n8.closure.PaperNormalizedValueBridge
import tmp.sheaf.n8.closure.PaperAllQPilotRegions
import tmp.sheaf.n8.closure.PaperP6ComparisonActual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperQPilotRegionPositivity

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.PaperAllQPilotRegions
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open LeanFormal.IUT.N8Closure.C7MassFormulaFinal
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block (S : SourceInitialThetaData l) : Type :=
  ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace
local instance rawAddHaar :
    (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu.IsAddHaarMeasure :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).addHaar

theorem raw_mu_eq_addHaar :
    (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu =
      (MeasureTheory.Measure.addHaar : Measure (Block S)) := rfl

theorem addHaar_isOpenPos :
    (MeasureTheory.Measure.addHaar : Measure (Block S)).IsOpenPosMeasure := by
  infer_instance

theorem qPilotRegionOf_isOpen (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) :
    IsOpen (qPilotRegionOf S q) := by
  have hIntOpen : IsOpen (Integers (C7MassFormulaZeroSorry.PaperKf S) : Set (C7MassFormulaZeroSorry.PaperKf S)) :=
    isOpen_integers S
  have hsmul : IsOpen (Set.image (fun x : C7MassFormulaZeroSorry.PaperKf S =>
      (q : C7MassFormulaZeroSorry.PaperKf S) * x)
      (Integers (C7MassFormulaZeroSorry.PaperKf S) : Set (C7MassFormulaZeroSorry.PaperKf S))) :=
    hIntOpen.smul q
  have hmap : IsOpenMap (fun y : C7MassFormulaZeroSorry.PaperKf S =>
      (C7QPilotRegionActual.e S).symm y) :=
    ((C7QPilotRegionActual.e S).symm.toContinuousLinearEquiv).isOpenMap
  unfold qPilotRegionOf
  exact hmap _ hsmul

theorem qPilotRegionOf_nonempty (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) :
    (qPilotRegionOf S q).Nonempty := by
  refine ⟨(C7QPilotRegionActual.e S).symm ((q : C7MassFormulaZeroSorry.PaperKf S) * 0), ?_⟩
  refine ⟨(q : C7MassFormulaZeroSorry.PaperKf S) * 0, ?_, rfl⟩
  refine ⟨0, ?_, rfl⟩
  exact (Integers (C7MassFormulaZeroSorry.PaperKf S)).zero_mem

theorem raw_mass_pos_of_mem_allQPilotRegions
    {T : Set (Block S)} (hT : T ∈ allQPilotRegions S) :
    0 < (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu T := by
  rcases hT with ⟨q, _hq, rfl⟩
  rw [raw_mu_eq_addHaar S]
  letI : (MeasureTheory.Measure.addHaar : Measure (Block S)).IsOpenPosMeasure :=
    addHaar_isOpenPos S
  exact (qPilotRegionOf_isOpen S q).measure_pos _ (qPilotRegionOf_nonempty S q)

end LeanFormal.IUT.N8Closure.PaperQPilotRegionPositivity

end
