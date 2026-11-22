import tmp.sheaf.n8.closure.PaperActualValuesBounded
import tmp.sheaf.n8.closure.PaperP6ComparisonActual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperAllQPilotRegions

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.PaperValuesBoundedActual
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open LeanFormal.IUT.N8Closure.PaperActualValuesBounded
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.LocalFieldIntegralUnits
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block (S : SourceInitialThetaData l) : Type :=
  ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

/-- The actual q-pilot region for an arbitrary unit q. -/
noncomputable def qPilotRegionOf (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) : Set (Block S) :=
  Set.image (fun y : C7MassFormulaZeroSorry.PaperKf S => (e S).symm y)
    (Set.image (fun x : C7MassFormulaZeroSorry.PaperKf S => (q : C7MassFormulaZeroSorry.PaperKf S) * x)
      (Integers (C7MassFormulaZeroSorry.PaperKf S) : Set (C7MassFormulaZeroSorry.PaperKf S)))

/-- All q-pilot regions with norm at most one. -/
def allQPilotRegions : Set (Set (Block S)) :=
  {T | ∃ q : (C7MassFormulaZeroSorry.PaperKf S)ˣ, ‖(q : C7MassFormulaZeroSorry.PaperKf S)‖ ≤ 1 ∧ T = qPilotRegionOf S q}

theorem q_smul_integers_subset_of_norm_le_one
    (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) (hq : ‖(q : C7MassFormulaZeroSorry.PaperKf S)‖ ≤ 1) :
    Set.image (fun x : C7MassFormulaZeroSorry.PaperKf S => (q : C7MassFormulaZeroSorry.PaperKf S) * x)
        (Integers (C7MassFormulaZeroSorry.PaperKf S) : Set (C7MassFormulaZeroSorry.PaperKf S)) ⊆
      (Integers (C7MassFormulaZeroSorry.PaperKf S) : Set (C7MassFormulaZeroSorry.PaperKf S)) := by
  rintro y ⟨x, hx, rfl⟩
  have hx' : ‖x‖ ≤ 1 := (mem_integers_iff _).mp hx
  apply (mem_integers_iff _).mpr
  rw [norm_mul]
  calc
    ‖(q : C7MassFormulaZeroSorry.PaperKf S)‖ * ‖x‖ ≤ 1 * 1 :=
      mul_le_mul hq hx' (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem qPilotRegionOf_subset_unitRef
    (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) (hq : ‖(q : C7MassFormulaZeroSorry.PaperKf S)‖ ≤ 1) :
    qPilotRegionOf S q ⊆ unitRef (places S) (tuple S) := by
  intro y hy
  rw [← e_preimage_integers S]
  rcases hy with ⟨x, hx, rfl⟩
  change C7QPilotRegionActual.e S ((C7QPilotRegionActual.e S).symm x) ∈
    (Integers (C7MassFormulaZeroSorry.PaperKf S) : Set (C7MassFormulaZeroSorry.PaperKf S))
  rw [(C7QPilotRegionActual.e S).apply_symm_apply]
  exact q_smul_integers_subset_of_norm_le_one S q hq hx

theorem allQPilotRegions_subset_hull :
    ∀ T ∈ allQPilotRegions S,
      T ⊆ c6Hull (places := places S) (tuple := tuple S)
        (rawData (places S) (tuple S)) := by
  intro T hT
  rcases hT with ⟨q, hq, rfl⟩
  exact Set.Subset.trans (qPilotRegionOf_subset_unitRef S q hq)
    (unitRef_subset_c6Hull S)

theorem allQPilotRegions_bounded :
    ∀ T ∈ allQPilotRegions S,
      Real.log
        ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal) ≤
        thetaLogVolume S :=
  fun T hT =>
    paperValueLog_le_theta_of_subset S T
      (allQPilotRegions_subset_hull S T hT)

end LeanFormal.IUT.N8Closure.PaperAllQPilotRegions

end
