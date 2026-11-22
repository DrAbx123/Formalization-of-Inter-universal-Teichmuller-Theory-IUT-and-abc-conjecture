/- U-R C2 theta-source hull, O-saturation definition (kurt, route section 5.3 J1 L419).

Lead ruling (ii): the theta region is defined as the O-saturation of the source generator:
  thetaSourceSpanO := { y * g | y in O },  g the pure-generator translate of the unit reference,
  O := arithmeticTupleCanonicalUnitReference.
Then O-action preserves the region BY DEFINITION once O is multiplicative; the hull is the closure.
The earlier thetaSourceSpan (possibleImages form) remains as a documented donor object.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKPacketActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaSourceHullOActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.LocalFieldProductHull
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- O is multiplicative: the canonical unit reference is closed under multiplication. -/
theorem mul_mem_canonicalUnitReference
    {x y : ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple}
    (hx : x ∈ arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple)
    (hy : y ∈ arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple) :
    x * y ∈ arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple := by
  classical
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, -, -⟩ :=
    exists_arithmeticTensorTuple_fieldProduct
      (p := (completionRationalPrime (nativeBadToKPlace T b)).val) (ksPlaces T b) ksTuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j) :=
    fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j =>
    FiniteDimensional.proper ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)
  rw [arithmeticTupleCanonicalUnitReference_eq (ksPlaces T b) ksTuple e] at hx hy ⊢
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨u * v, ?_, ?_⟩
  · intro j
    change ‖(u * v) j‖ ≤ 1
    rw [Pi.mul_apply, norm_mul]
    simpa using mul_le_mul (hu j) (hv j) (norm_nonneg _) (by norm_num)
  · exact map_mul e.symm u v

/-- The pure-generator translate of the unit reference. -/
noncomputable def sourceGenerator : ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple :=
  arithmeticTupleTprod (ksPlaces T b) ksTuple
    (Function.update 1 () ((urCeilData (l := l) T b).localGenerator ()))

/-- O-saturated theta source region: { y * g | y in O }. -/
noncomputable def thetaSourceSpanO : Set (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple) :=
  {s | ∃ y ∈ arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple,
    s = y * sourceGenerator (l := l) T b}

/-- The O-saturated theta-source hull. -/
noncomputable def thetaSourceHullO : Set (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple) :=
  closure (thetaSourceSpanO (l := l) T b)

/-- The generator itself lies in the O-saturated span (y = 1). -/
theorem sourceGenerator_mem_spanO
    (hOne : (1 : ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple) ∈
      arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple) :
    sourceGenerator (l := l) T b ∈ thetaSourceSpanO (l := l) T b := by
  refine ⟨1, hOne, ?_⟩
  simp [sourceGenerator]

/-- O-action preserves the O-saturated span (this is the route L419 O-saturation step). -/
theorem O_smul_spanO_subset
    {y : ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple}
    (hy : y ∈ arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple) :
    y • thetaSourceSpanO (l := l) T b ⊆ thetaSourceSpanO (l := l) T b := by
  rintro s ⟨z, ⟨w, hw, rfl⟩, rfl⟩
  refine ⟨y * w, mul_mem_canonicalUnitReference (l := l) T b hy hw, ?_⟩
  noncomm_ring

/-- The span is contained in its closure. -/
theorem thetaSourceSpanO_subset_hull :
    thetaSourceSpanO (l := l) T b ⊆ thetaSourceHullO (l := l) T b :=
  subset_closure

end LeanFormal.IUT.XiFPaper.Mzk1URThetaSourceHullOActual
end