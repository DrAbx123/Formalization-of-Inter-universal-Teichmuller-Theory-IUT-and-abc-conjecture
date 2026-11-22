/- U-R C2 theta-source hull (kurt, route section 5.3 J1 L416-423).

Route reading: theta region = integral span / holomorphic hull of the actual source images; the
source generator lies in the hull and O-action preserves the region, so source q-membership yields
the whole q-root lattice inside the theta region (O-saturation). Containment direction:
qRoot subset thetaHull; urCeilC/j1_ksRootCoeff_le_urCeilC is only for the MEASURE upper region.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKPacketActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaSourceHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKPacketActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The actual source image span at the ceiling generator (theta-source side, route J1),
with the measure-space instances passed explicitly. -/
noncomputable def thetaSourceSpan
    (hMeas : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b))
    (hBorel : ∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)) :
    Set (ksBlock T b) := by
  letI := hMeas
  letI := hBorel
  exact ksThetaPossibleImages (l := l) T b ((urCeilData (l := l) T b).localGenerator ())

/-- The theta-source hull: closure of the source image span. -/
noncomputable def thetaSourceHull
    (hMeas : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b))
    (hBorel : ∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)) :
    Set (ksBlock T b) :=
  closure (thetaSourceSpan (l := l) T b hMeas hBorel)

/-- The source span is contained in its hull. -/
theorem thetaSourceSpan_subset_hull
    (hMeas : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b))
    (hBorel : ∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)) :
    thetaSourceSpan (l := l) T b hMeas hBorel ⊆ thetaSourceHull (l := l) T b hMeas hBorel :=
  subset_closure

open LeanFormal.IUT.LocalFieldProductHull in
/-- The canonical unit reference contains one (via the product-field presentation). -/
theorem one_mem_arithmeticTupleCanonicalUnitReference :
    (1 : ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple) ∈
      arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple := by
  classical
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, -, -⟩ :=
    exists_arithmeticTensorTuple_fieldProduct (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
      (ksPlaces T b) ksTuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j) :=
    fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j =>
    FiniteDimensional.proper ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)
  rw [arithmeticTupleCanonicalUnitReference_eq (ksPlaces T b) ksTuple e]
  refine ⟨e 1, ?_, ?_⟩
  · intro j
    have h1 : e (1 : ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple) =
        (1 : (j : J) → E j) := map_one e
    rw [h1]
    simp
  · exact e.symm_apply_apply 1


/-- The source generator (pure generator translate) lies in the theta-source span:
take phi = id and x = 1 in the possible-images membership. -/
theorem sourceGenerator_mem_span
    (hMeas : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b))
    (hBorel : ∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)) :
    arithmeticTupleTprod (ksPlaces T b) ksTuple
        (Function.update 1 () ((urCeilData (l := l) T b).localGenerator ())) ∈
      thetaSourceSpan (l := l) T b hMeas hBorel := by
  unfold thetaSourceSpan
  change arithmeticTupleTprod (ksPlaces T b) ksTuple
      (Function.update 1 () ((urCeilData (l := l) T b).localGenerator ())) ∈
    LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleStepVPossibleImages
      (ksPlaces T b) ksTuple () ((urCeilData (l := l) T b).localGenerator ())
      (ksThetaPhi (l := l) T b)
  unfold LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleStepVPossibleImages
  refine ⟨LinearEquiv.refl ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]
      (ksBlock T b), ?_, 1, one_mem_arithmeticTupleCanonicalUnitReference (l := l) T b, ?_⟩
  · intro u hu
    simpa using hu
  · simp

end LeanFormal.IUT.XiFPaper.Mzk1URThetaSourceHullActual
end