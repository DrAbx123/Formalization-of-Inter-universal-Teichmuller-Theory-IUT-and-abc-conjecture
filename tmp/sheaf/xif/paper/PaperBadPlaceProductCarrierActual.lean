import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-! # Paper bad-place product carrier (S13 first half)

The dependent rational prime p_b means there is no single
ArithmeticTensorTupleBlock over all bad places.  This file defines the actual
global carrier as the product of the per-b actual blocks

  PaperBadPlaceProductCarrier T = (b : Bad (nativePlaceSelection T)) → qVFamTensorBlock T b,

with the actual projection to every factor, product extensionality, and the
actual per-b block/geometry data (dependent place, tensor places, tuple).

Haar and normalized log-volume are deliberately not constructed here; they are
left to the Kummer half.

No single fixed-p tensor block is claimed.  No fake equality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperBadPlaceProductCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual global carrier: product of the actual per-b tensor blocks. -/
abbrev PaperBadPlaceProductCarrier : Type :=
  (b : Bad (nativePlaceSelection T)) → qVFamTensorBlock T b

/-- The actual projection of the product carrier to the b-th block. -/
def paperProductProjection
    (b : Bad (nativePlaceSelection T)) :
    PaperBadPlaceProductCarrier T → qVFamTensorBlock T b :=
  fun x => x b

/-- Projection computes the b-th coordinate. -/
theorem paperProductProjection_apply
    (b : Bad (nativePlaceSelection T)) (x : PaperBadPlaceProductCarrier T) :
    paperProductProjection T b x = x b := rfl

/-- Build a product element from its per-b coordinates. -/
def paperProductMk
    (x : (b : Bad (nativePlaceSelection T)) → qVFamTensorBlock T b) :
    PaperBadPlaceProductCarrier T :=
  x

/-- Projection after product formation is the coordinate. -/
theorem paperProductProjection_mk
    (b : Bad (nativePlaceSelection T))
    (x : (b : Bad (nativePlaceSelection T)) → qVFamTensorBlock T b) :
    paperProductProjection T b (paperProductMk T x) = x b := rfl

/-- Product extensionality: equal projections give equal product elements. -/
theorem paperProduct_ext
    {x y : PaperBadPlaceProductCarrier T}
    (h : ∀ b, paperProductProjection T b x = paperProductProjection T b y) :
    x = y :=
  funext h

/-- Actual per-b block data: the block, its rational prime, tensor places and tuple. -/
structure PaperBadPlaceProductBlockData
    (b : Bad (nativePlaceSelection T)) where
  block : Type
  block_eq : block = qVFamTensorBlock T b
  p : Nat
  p_eq : p = qVFamTensorP T b
  tensorPlaceIndex : Type
  tensorPlaceIndex_eq : tensorPlaceIndex = Unit
  tensorPlaces : tensorPlaceIndex → FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b)
  tensorTuple : tensorPlaceIndex

/-- The actual per-b block data constructor. -/
noncomputable def paperBadPlaceProductBlockData
    (b : Bad (nativePlaceSelection T)) :
    PaperBadPlaceProductBlockData T b where
  block := qVFamTensorBlock T b
  block_eq := rfl
  p := qVFamTensorP T b
  p_eq := rfl
  tensorPlaceIndex := Unit
  tensorPlaceIndex_eq := rfl
  tensorPlaces := fun _ => qVFamTensorPlaces T b () (qVFamTensorTuple ())
  tensorTuple := ()

/-- Actual S13 product-carrier data. -/
structure PaperBadPlaceProductData where
  projection : (b : Bad (nativePlaceSelection T)) →
    PaperBadPlaceProductCarrier T → qVFamTensorBlock T b
  projection_eq : projection = fun b => paperProductProjection T b
  blockData : (b : Bad (nativePlaceSelection T)) →
    PaperBadPlaceProductBlockData T b
  blockData_eq : blockData = paperBadPlaceProductBlockData T

/-- The actual product carrier/projection/block data constructor. -/
noncomputable def paperBadPlaceProductData :
    PaperBadPlaceProductData T where
  projection := fun b x => x b
  projection_eq := rfl
  blockData := paperBadPlaceProductBlockData T
  blockData_eq := rfl

end LeanFormal.IUT.XiFPaper.PaperBadPlaceProductCarrierActual

end
