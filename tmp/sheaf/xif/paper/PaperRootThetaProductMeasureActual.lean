import tmp.sheaf.xif.paper.PaperRootThetaNormBoundActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.PaperRootThetaProductCarrierActual

/-!
# Actual finite image measure on the root Theta product carrier

The product of algebraic closures is not locally compact, so it carries no Haar
measure.  The actual root Theta image is finite.  This file constructs the actual
finite Dirac measure supported on that image, proves that the product unit ball
has positive finite measure under the q-unit norm hypothesis, and records the
Haar gap explicitly instead of calling the Dirac measure Haar.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootThetaProductMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaProductCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaNormBoundActual
open MeasureTheory

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable [MeasurableSpace (RootThetaProductCarrier (G := G))]

/-- Actual finite Dirac measure supported on the root Theta image. -/
noncomputable def rootThetaImageMeasure :
    Measure (RootThetaProductCarrier (G := G)) :=
  ∑ j : ThetaLabel (l := l),
    Measure.dirac (rootThetaProductImagePoint (G := G) j)

/-- The image measure of the product unit ball is the number of signed labels,
under the q-unit norm condition. -/
theorem rootThetaImageMeasure_unitBall
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    rootThetaImageMeasure (G := G) (rootThetaUnitBall (G := G)) =
      (Fintype.card (ThetaLabel (l := l)) : ENNReal) := by
  unfold rootThetaImageMeasure
  rw [Measure.finsetSum_apply]
  rw [show (Fintype.card (ThetaLabel (l := l)) : ENNReal) =
    ∑ _ : ThetaLabel (l := l), (1 : ENNReal) by simp]
  apply Finset.sum_congr rfl
  intro j _
  have hmem : rootThetaProductImagePoint (G := G) j ∈ rootThetaUnitBall (G := G) :=
    rootThetaProductImageSet_subset_unitBall_of_hq (G := G) hq
      ⟨j, rfl⟩
  rw [Measure.dirac_apply_of_mem hmem]

/-- The product unit ball has positive finite image measure under hq. -/
theorem rootThetaImageMeasure_unitBall_pos_lt_top
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    0 < rootThetaImageMeasure (G := G) (rootThetaUnitBall (G := G)) ∧
      rootThetaImageMeasure (G := G) (rootThetaUnitBall (G := G)) < ⊤ := by
  rw [rootThetaImageMeasure_unitBall (G := G) hq]
  constructor
  · haveI : Nonempty (ThetaLabel (l := l)) :=
      ⟨⟨oneLabel l, by rw [oneLabel_val]; norm_num⟩⟩
    exact_mod_cast Fintype.card_pos
  · exact ENNReal.natCast_lt_top _

/-- Exact missing actual Haar measure on the algebraic-closure product.  The
Dirac image measure below is not Haar. -/
structure RootThetaProductHaarGap where
  haarCarrier : Type
  [haarMeasurable : MeasurableSpace haarCarrier]
  haarMeasure : Measure haarCarrier
  haar_is_add_haar : Prop
  rootCarrier_embeds : Prop
  image_measure_compat : Prop

/-- Exact missing product Haar object. -/
def RootThetaProductHaarGapRequired : Prop :=
  Nonempty (RootThetaProductHaarGap)

end LeanFormal.IUT.XiFPaper.PaperRootThetaProductMeasureActual

end