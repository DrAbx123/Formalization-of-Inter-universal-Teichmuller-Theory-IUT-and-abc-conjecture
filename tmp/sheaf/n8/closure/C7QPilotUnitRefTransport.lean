import tmp.sheaf.n8.closure.C6UnitRefNormalized
import tmp.sheaf.n8.closure.C7QPilotRegionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlockFields

/-!
# C7 q-pilot unit-reference transport

Use a canonical algebra equivalence `e : Block ≃ₐ[Qp] ((j:J)→E j)` from the
production field-product existence theorem; `arithmeticTupleCanonicalUnitReference_eq`
then gives `e '' unitRef = unitRegion (K:=E)`.  The one-factor identification
with `Integers` remains a named obligation. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7QPilotUnitRefTransport

universe u v

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota → Type} [∀ i, Fintype (V i)]
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)

noncomputable def unitRefSet : Set (ArithmeticTensorTupleBlock places tuple) :=
  arithmeticTupleCanonicalUnitReference places tuple

theorem canonicalAlgEquiv_image_unitRef
    {J : Type (max u v)} [Fintype J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    Set.image (fun y => e y) (unitRefSet places tuple) = unitRegion (K := E) := by
  rw [unitRefSet, arithmeticTupleCanonicalUnitReference_eq places tuple e]
  unfold arithmeticTupleUnitReferencePullback
  rw [Set.image_image]
  simp only [AlgEquiv.apply_symm_apply]
  change id '' unitRegion (K := E) = unitRegion (K := E)
  exact Set.image_id _

section Paper

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7QPilotMassActual

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

/-- Exact one-factor canonical algebra equivalence target. -/
def OneFactorCanonicalAlgEquiv : Prop :=
  Nonempty (ArithmeticTensorTupleBlock (C7QPilotRegionActual.places S) (C7QPilotRegionActual.tuple S) ≃ₐ[ℚ_[pNat S]]
    (Unit → PaperKf S))

/-- Unit-reference image under a supplied one-factor algebra equivalence: the
canonical product unit region over `Unit` (pointwise integers). -/
def UnitRefImageTransportOneFactor
    (eAlg : ArithmeticTensorTupleBlock (C7QPilotRegionActual.places S) (C7QPilotRegionActual.tuple S) ≃ₐ[ℚ_[pNat S]]
      (Unit → PaperKf S)) : Prop :=
  Set.image (fun y => eAlg y) (unitRefSet (C7QPilotRegionActual.places S) (C7QPilotRegionActual.tuple S)) =
    {x : Unit → PaperKf S | ∀ i, x i ∈ (Integers (PaperKf S) : Set (PaperKf S))}

end Paper

end LeanFormal.IUT.N8Closure.C7QPilotUnitRefTransport

end