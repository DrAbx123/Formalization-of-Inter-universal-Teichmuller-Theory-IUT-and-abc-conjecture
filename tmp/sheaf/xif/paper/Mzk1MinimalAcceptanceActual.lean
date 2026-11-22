/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-!
# P3 minimal acceptance: actual qVFam fractional lattice and its hull containment

Status: PARTIAL/actual-node.  This file records one actual finite-generated
lattice `LambdaG` on the qVFam tensor block, proves it is contained in the
paper non-zero-label image (hence in the closure hull), and proves the exact
normalized log-volume formula conditional on an actual
`ArithmeticTuplePureFractionalScalingData` for the paper coefficient family.

Not claimed: Mzk1PaperFaithfulHullActual is not green in this snapshot; the
local hull below is exactly closure(paperRootThetaImageNZ).  The coefficient
scaling data for `paperRootCoefficientFamily` and the trace-dual same-volume
bridge are recorded as GAPs in coord/P3-MINIMAL-ACCEPTANCE.md.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1MinimalAcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The actual finite-generated fractional lattice `LambdaG` at c_root, in
the qVFam tensor block.  It is the product of the actual fractional lattice
with the holomorphic integers; its generators are the pure-tensor generators
supplied by the actual data below. -/
noncomputable def LambdaG : Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b) :=
  arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b) *
    arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple

theorem LambdaG_eq_paperLambdaORegion :
    (LambdaG (l := l) T b : Set (qVFamTensorBlock T b)) =
      paperLambdaORegion (l := l) T b (paperRootCoefficientFamily (l := l) T b) :=
  rfl

/-- `LambdaG` is the j=1 paper non-zero-label region, hence contained in the
paper non-zero-label image. -/
theorem LambdaG_subset_paperRootThetaImageNZ :
    (LambdaG (l := l) T b : Set (qVFamTensorBlock T b)) ⊆
      paperRootThetaImageNZ (l := l) T b := by
  intro x hx
  rw [LambdaG_eq_paperLambdaORegion] at hx
  apply Set.mem_iUnion.mpr
  refine ⟨⟨oneLabel (l := l), paperOneLabel_ne_zero (l := l)⟩, ?_⟩
  unfold paperRootThetaRegionNZ
  rw [gaussExponent_oneLabel (l := l)]
  simpa [paperLambdaORegion, one_mul] using hx

/-- Local honest hull: closure of the paper non-zero-label image.  This is the
same set intended by Mzk1PaperFaithfulHullActual; that file is not green in
this snapshot, so we do not pretend to import its theorem. -/
noncomputable def paperFaithfulThetaHullNZ : Set (qVFamTensorBlock T b) :=
  closure (paperRootThetaImageNZ (l := l) T b)

theorem LambdaG_subset_paperFaithfulThetaHullNZ :
    (LambdaG (l := l) T b : Set (qVFamTensorBlock T b)) ⊆
      paperFaithfulThetaHullNZ (l := l) T b := by
  intro x hx
  exact subset_closure (LambdaG_subset_paperRootThetaImageNZ (l := l) T b hx)

/-- Exact normalized log-volume of `LambdaG`, conditional on the actual
pure-fractional scaling data for the paper coefficient family.  The formula
is `-(sum_i c_i) log p`; this is the actual Haar formula, not an integer toy. -/
theorem LambdaG_normalizedLogVolume
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (data : ArithmeticTuplePureFractionalScalingData (qVFamTensorPlaces T b)
      qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b)) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
      mu (LambdaG (l := l) T b : Set (qVFamTensorBlock T b)) =
      -((∑ i : qVFamTensorV, paperRootCoefficientFamily (l := l) T b i) *
        Real.log (qVFamTensorP T b : Real)) := by
  simpa [LambdaG] using
    arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
      mu (data := data)

-- The ratio form mu(LambdaG)/mu(O_i) = p^r is obtained by exponentiating
-- the normalized formula.  With d = finrank of the qVFam tensor block and
-- c_i = paperRootCoefficientFamily T b i, the exponent is
--   r = -d * (sum_i c_i).
-- The source data argument is an actual construction obligation; until it
-- is constructed this theorem is conditional (see the acceptance doc).

def acceptanceRows : List (String × String) :=
  [ ("LambdaG_subset_paperRootThetaImageNZ", "actual containment"),
    ("LambdaG_subset_paperFaithfulThetaHullNZ", "closure hull containment"),
    ("LambdaG_normalizedLogVolume", "conditional on actual scaling data"),
    ("mu-ratio / trace-dual same volume", "GAP") ]

theorem acceptanceRows_length : acceptanceRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1MinimalAcceptanceActual
