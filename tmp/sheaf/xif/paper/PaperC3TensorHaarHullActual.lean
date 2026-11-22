import tmp.sheaf.xif.paper.PaperC3TensorGeometryActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-!
# Actual Haar measure and hull on the C3 tensor geometry
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.PaperC3TensorHaarHullActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open MeasureTheory

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (K := K) (p := p) V)

/-- Actual tensor places from the C3 geometry. -/
abbrev paperC3TensorPlaces (i : PaperTensorIndex (V := V)) :
    PaperTensorPlaceIndex (V := V) i → FinitePlaceAtPrime K p :=
  paperTensorPlaces (K := K) (p := p) G i

/-- Actual tensor tuple. -/
def paperC3TensorTuple (i : PaperTensorIndex (V := V)) :
    PaperTensorPlaceIndex (V := V) i := ()

/-- Actual tensor block. -/
abbrev paperC3TensorBlock : Type :=
  ArithmeticTensorTupleBlock (paperC3TensorPlaces G) (paperC3TensorTuple (V := V))

variable [MeasurableSpace (paperC3TensorBlock (K := K) (p := p) G)]
variable [BorelSpace (paperC3TensorBlock (K := K) (p := p) G)]

/-- Actual additive Haar measure on the tensor block. -/
noncomputable def paperC3TensorHaar : Measure (paperC3TensorBlock (K := K) (p := p) G) :=
  Measure.addHaar

instance paperC3TensorHaar_isAddHaar :
    Measure.IsAddHaarMeasure (paperC3TensorHaar G) := by
  unfold paperC3TensorHaar
  infer_instance

/-- Actual canonical hull in the tensor block. -/
def paperC3TensorHull : Set (paperC3TensorBlock (K := K) (p := p) G) :=
  arithmeticTupleCanonicalHull (paperC3TensorPlaces G) (paperC3TensorTuple (V := V))

/-- Actual normalized Haar log-volume of the hull. -/
noncomputable def paperC3TensorHullLogVolume : Real :=
  arithmeticTupleNormalizedLogVolume (paperC3TensorPlaces G) (paperC3TensorTuple (V := V))
    (paperC3TensorHaar G) (paperC3TensorHull G)

/-- Actual hull has positive finite Haar measure. -/
theorem paperC3TensorHull_measure_pos_lt_top :
    0 < paperC3TensorHaar G (paperC3TensorHull G) ∧
      paperC3TensorHaar G (paperC3TensorHull G) < ⊤ :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (paperC3TensorPlaces G) (paperC3TensorTuple (V := V)) (paperC3TensorHaar G)).1

/-- The hull log-volume is the actual normalized hull measure. -/
theorem paperC3TensorHullLogVolume_eq :
    paperC3TensorHullLogVolume (K := K) (p := p) G =
      arithmeticTupleNormalizedLogVolume (paperC3TensorPlaces G)
        (paperC3TensorTuple (V := V)) (paperC3TensorHaar G) (paperC3TensorHull G) := rfl

end LeanFormal.IUT.XiFPaper.PaperC3TensorHaarHullActual

end