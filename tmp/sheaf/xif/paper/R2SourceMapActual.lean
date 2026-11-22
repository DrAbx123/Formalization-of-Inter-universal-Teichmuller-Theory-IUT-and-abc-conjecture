/- R2 SOURCE MAP (route 4.2 step 3): actual P5 source objects of Mzk1URPacketActual
(reference lattice, Phi action family, theta source span) compared with the actual tensor
block packet hull.  The source object is already the one-slot ArithmeticTensorTupleBlock, so
the comparison map is the identity and the theta-image coverage is the accepted donor
p6_possibleImages_subset_packetHull.  No fake equality; no new data.
-/
import tmp.sheaf.xif.paper.Mzk1URPacketActual
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.R2SourceMapActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P6SourceFieldsActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1URPacketActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance r2SourceMeasurable : MeasurableSpace (urBlock X) := borel _
local instance r2SourceBorel : BorelSpace (urBlock X) := ⟨rfl⟩

/-- The actual P5 source-to-tensor comparison map (identity on the one-slot block). -/
def sourceToTensor : urBlock X → urBlock X := id

theorem sourceToTensor_referenceLattice :
    sourceToTensor X '' urReferenceLattice X = urReferenceLattice X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem sourceToTensor_phi :
    urPhi X = p6Phi (urPlaces X) (urTuple X) := rfl

/-- The actual theta possible images are covered by the actual tensor packet hull. -/
theorem thetaImage_coverage
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[urP X] (E j)]
    [∀ j, FiniteDimensional ℚ_[urP X] (E j)]
    [∀ j, ProperSpace (E j)]
    (e : urBlock X ≃ₐ[ℚ_[urP X]] ((j : J) → E j))
    (istar : Unit)
    (varpi : CommonPrimeCompletion ((urPlaces X) istar ((urTuple X) istar))) :
    arithmeticTupleStepVPossibleImages (urPlaces X) (urTuple X) istar varpi (urPhi X) ⊆
      p6PacketHull (urPlaces X) (urTuple X) e istar varpi := by
  exact p6_possibleImages_subset_packetHull (urPlaces X) (urTuple X) e istar varpi

#print axioms sourceToTensor_referenceLattice
#print axioms sourceToTensor_phi
#print axioms thetaImage_coverage
end LeanFormal.IUT.XiFPaper.R2SourceMapActual