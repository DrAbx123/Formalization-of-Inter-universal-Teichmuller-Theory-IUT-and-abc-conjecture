import tmp.sheaf.n8.closure.PaperNormalizedValueBridge
import tmp.sheaf.n8.closure.PaperAllQPilotRegions
import tmp.sheaf.n8.closure.C7MassFormulaFinal

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

namespace LeanFormal.IUT.N8Closure.PaperQPilotRegionPositivity2

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.PaperAllQPilotRegions
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open LeanFormal.IUT.N8Closure.C7MassFormulaFinal
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
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

theorem qPilotRegionOf_eq_preimage (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) :
    qPilotRegionOf S q =
      (fun x : Block S => (C7QPilotRegionActual.e S) x) ⁻¹'
        (Set.image (fun y : C7MassFormulaZeroSorry.PaperKf S =>
          (q : C7MassFormulaZeroSorry.PaperKf S) * y)
          (Integers (C7MassFormulaZeroSorry.PaperKf S) : Set (C7MassFormulaZeroSorry.PaperKf S))) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨(C7QPilotRegionActual.e S) x, hx, (C7QPilotRegionActual.e S).symm_apply_apply x⟩

theorem qPilotRegionOf_isOpen (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) :
    IsOpen (qPilotRegionOf S q) := by
  rw [qPilotRegionOf_eq_preimage S q]
  have hIntOpen : IsOpen (Integers (C7MassFormulaZeroSorry.PaperKf S) :
      Set (C7MassFormulaZeroSorry.PaperKf S)) := isOpen_integers S
  have hsmul : IsOpen (Set.image (fun y : C7MassFormulaZeroSorry.PaperKf S =>
      (q : C7MassFormulaZeroSorry.PaperKf S) * y)
      (Integers (C7MassFormulaZeroSorry.PaperKf S) :
        Set (C7MassFormulaZeroSorry.PaperKf S))) :=
    hIntOpen.smul q
  exact ((C7QPilotRegionActual.e S).toContinuousLinearEquiv.continuous).isOpen_preimage _ hsmul

theorem qPilotRegionOf_nonempty (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) :
    (qPilotRegionOf S q).Nonempty := by
  refine ⟨(C7QPilotRegionActual.e S).symm ((q : C7MassFormulaZeroSorry.PaperKf S) * 0), ?_⟩
  refine ⟨(q : C7MassFormulaZeroSorry.PaperKf S) * 0, ?_, rfl⟩
  exact ⟨0, (Integers (C7MassFormulaZeroSorry.PaperKf S)).zero_mem, rfl⟩

theorem raw_mu_eq_addHaar :
    (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu =
      (MeasureTheory.Measure.addHaar : Measure (Block S)) := rfl

theorem addHaar_isOpenPos :
    (MeasureTheory.Measure.addHaar : Measure (Block S)).IsOpenPosMeasure := by
  infer_instance

theorem raw_mass_pos_of_mem_allQPilotRegions
    {T : Set (Block S)} (hT : T ∈ allQPilotRegions S) :
    0 < (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu T := by
  rcases hT with ⟨q, _hq, rfl⟩
  rw [raw_mu_eq_addHaar S]
  letI : (MeasureTheory.Measure.addHaar : Measure (Block S)).IsOpenPosMeasure :=
    addHaar_isOpenPos S
  exact (qPilotRegionOf_isOpen S q).measure_pos _ (qPilotRegionOf_nonempty S q)

end LeanFormal.IUT.N8Closure.PaperQPilotRegionPositivity2

end
