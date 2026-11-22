import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! Mainline (A481 literal-object rewiring): the literal IQ carrier is the rational span
  of the arithmetic log-shell tensor region over a finite family of finite places
  (actual completion packets, no value-realization model).  On it we define the literal
  unit/hull regions, the literal log-shell point datum and the literal normalized
  comparison region, and state the two comparison propositions on the literal carrier.
  The Haar log-volume is carried as an explicit region functional with its literal
  volume axioms (`LiteralCarrierAxioms`) — the product-Haar construction is the next
  step, not assumed silently. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LiteralIQCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]

/-- Literal IQ carrier: rational span of the arithmetic log-shell tensor region
  (the local arithmetic side of `IQ(S±; n, ◦D^vdash)`, no value model). -/
abbrev LiteralIQCarrier (places : (i : ι) → V i → FinitePlaceAtPrime K p) : Type _ :=
  arithmeticIQCarrier places

/-- The literal compact log-shell region inside the literal IQ carrier. -/
def literalUnitRegion (places : (i : ι) → V i → FinitePlaceAtPrime K p) :
    Set (LiteralIQCarrier places) :=
  {x | (x : ArithmeticPacketTensor places) ∈ arithmeticTensorLogRegion places}

/-- The literal hull is the log-shell region (paper hull of the image union). -/
def literalHull (places : (i : ι) → V i → FinitePlaceAtPrime K p) :
    Set (LiteralIQCarrier places) :=
  literalUnitRegion places

/-- Multiplicative scaling by the rational scaling parameter on the literal carrier. -/
def literalScaleShift (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (scale : ℚ) : LiteralIQCarrier places → LiteralIQCarrier places :=
  fun x => scale • x

/-- Literal paper data: the image of `x = a/c` under the Hodge-theater/prime-strip
  composite (explicit datum; its construction is the next literal object) and the
  scaling parameter. -/
structure LiteralIQData (places : (i : ι) → V i → FinitePlaceAtPrime K p) where
  logShellPoint : Nat → Nat → Nat → LiteralIQCarrier places
  scale : ℚ
  scale_pos : 0 < scale

/-- Literal normalized comparison region: scaled log-shell region together with the
  literal log-shell point (the paper `λ·O` region of Remark 3.9.5). -/
def literalNormalizedComparisonRegion (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (D : LiteralIQData places) (a b c : Nat) : Set (LiteralIQCarrier places) :=
  literalScaleShift places D.scale ''
    (literalUnitRegion places ∪ {D.logShellPoint a b c})

/-- Literal volume axioms: the region log-volume functional is monotone, normalized on
  the unit region, contraction-normalized on its scaling image, and the hull sits in the
  scaled unit region.  These are the literal Haar facts to be proved from the product
  measure (explicit fields, not hidden axioms). -/
structure LiteralCarrierAxioms (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (D : LiteralIQData places)
    (volume : Set (LiteralIQCarrier places) → ENNReal) : Prop where
  logVolume_mono : ∀ {S T : Set (LiteralIQCarrier places)}, S ⊆ T → volume S ≤ volume T
  unitRegion_logVolume_lt_top : volume (literalUnitRegion places) < ⊤
  scaleShift_unitRegion_logVolume_le :
    volume (literalScaleShift places D.scale '' literalUnitRegion places) ≤
      volume (literalUnitRegion places)
  hull_subset_scaleShift :
    literalHull places ⊆ literalScaleShift places D.scale '' literalUnitRegion places

/-- The literal IQ interface instance on the literal carrier. -/
def literalIQInterface (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (D : LiteralIQData places)
    (volume : Set (LiteralIQCarrier places) → ENNReal)
    (A : LiteralCarrierAxioms places D volume) :
    IQHullLogVolumeInterface (LiteralIQCarrier places) where
  imageSet := literalUnitRegion places
  hull := literalHull places
  imageSet_subset_hull := by
    intro x hx
    exact hx
  logVolume := volume
  logVolume_mono := A.logVolume_mono
  unitRegion := literalUnitRegion places
  scaleShift := literalScaleShift places D.scale
  hull_subset_scaleShift := A.hull_subset_scaleShift
  unitRegion_logVolume_lt_top := A.unitRegion_logVolume_lt_top
  scaleShift_unitRegion_logVolume_le := A.scaleShift_unitRegion_logVolume_le

/-- The two Cor 3.12 comparison propositions, stated literally on the carrier region. -/
structure LiteralEpsilonComparison (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (D : LiteralIQData places) (W : IQHullLogVolumeInterface (LiteralIQCarrier places))
    (epsilon : Real) : Prop where
  height_le_normalizedRegionVolume : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) *
        (W.logVolume (normalizedComparisonRegion W D.logShellPoint a b c)).toReal
  regionVolume_le_normalizedWeight : ∃ D0 : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (normalizedComparisonRegion W D.logShellPoint a b c)).toReal ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D0

/-- The literal per-epsilon comparison gives the standard bridge comparison data on the
  literal interface (the literal region is definitionally the standard normalized region
  of the literal interface). -/
def literalEpsilonComparisonToStandard
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (D : LiteralIQData places)
    (volume : Set (LiteralIQCarrier places) → ENNReal)
    (A : LiteralCarrierAxioms places D volume)
    (epsilon : Real)
    (h : LiteralEpsilonComparison places D
      (literalIQInterface places D volume A) epsilon) :
    Cor312EpsilonArithmeticComparison (literalIQInterface places D volume A) epsilon where
  logShellPoint := D.logShellPoint
  height_le_normalizedRegionVolume := h.height_le_normalizedRegionVolume
  regionVolume_le_normalizedWeight := h.regionVolume_le_normalizedWeight
/-- Literal comparison family on the literal IQ carrier yields the bridge interface and
  hence conditional ABC (no value-realization model involved). -/
theorem abcConjecture_of_literalComparisonFamily
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (D : LiteralIQData places)
    (volume : Set (LiteralIQCarrier places) → ENNReal)
    (A : LiteralCarrierAxioms places D volume)
    (h : ∀ epsilon : Real, 0 < epsilon →
      LiteralEpsilonComparison places D
        (literalIQInterface places D volume A) epsilon) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture
    { carrier := LiteralIQCarrier places
      hullData := literalIQInterface places D volume A
      epsilonComparison := fun epsilon hepsilon =>
        literalEpsilonComparisonToStandard places D volume A epsilon
          (h epsilon hepsilon) }

end

end LeanFormal.IUT.XiFPaper.Mzk1LiteralIQCarrierActual