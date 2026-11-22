import tmp.sheaf.n8.closure.C7OneFactorAlgEquivConstructed2
import tmp.sheaf.n8.closure.C7QPilotUnitRefTransport
import tmp.sheaf.n8.closure.C6UnitRefNormalized
import Mathlib.Algebra.Ring.Equiv

/-!
# C7 mass formula closure attempt

Construct the one-factor algebra equivalence to `(Unit → Kf)`, close the
unit-reference image transport, and isolate the remaining normalized-Haar
comparison needed for the q-pilot mass formula. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7MassFormulaClosed

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7OneFactorAlgEquivConstructed2
open LeanFormal.IUT.N8Closure.C7QPilotUnitRefTransport
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

noncomputable def piUnitAlgEquiv : (Unit → PaperKf S) ≃ₐ[ℚ_[pNat S]] PaperKf S := by
  refine { RingEquiv.piUnique (fun _ : Unit => PaperKf S) with
    commutes' := ?_ }
  intro r
  simp [RingEquiv.piUnique]

noncomputable def eAlgPi :
    ArithmeticTensorTupleBlock (places S) (tuple S) ≃ₐ[ℚ_[pNat S]]
      (Unit → PaperKf S) :=
  (oneFactorAlgEquiv S).trans (piUnitAlgEquiv S).symm

theorem unitRef_image_pointwise_integers :
    Set.image (fun y => eAlgPi S y)
      (unitRefSet (places S) (tuple S)) =
      {x : Unit → PaperKf S | ∀ i, x i ∈ (Integers (PaperKf S) : Set (PaperKf S))} :=
  unitRefImageTransportOneFactor_of_algEquiv S (eAlgPi S)

theorem unitRef_image_integers :
    Set.image (fun y => piUnitAlgEquiv S (eAlgPi S y))
      (unitRefSet (places S) (tuple S)) =
      (Integers (PaperKf S) : Set (PaperKf S)) := by
  rw [← Set.image_image]
  rw [unitRef_image_pointwise_integers S]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [piUnitAlgEquiv] using hy ()
  · intro hx
    refine ⟨(fun _ => x), ?_, ?_⟩
    · intro i
      simpa using hx
    · simp [piUnitAlgEquiv]

/-- Exact normalized-Haar comparison left after the image transport. -/
def QPilotMassFormula : Prop :=
  (c6UnitRefNormalizedData (places S) (tuple S)
    (qPilotRegion S)).toReal = ‖q S‖ ^ (C7QPilotMassActual.d S)

end LeanFormal.IUT.N8Closure.C7MassFormulaClosed

end