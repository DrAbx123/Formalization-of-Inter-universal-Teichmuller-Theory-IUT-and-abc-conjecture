import tmp.sheaf.xif.paper.S156QPilotSideObjectActual
import tmp.sheaf.xif.paper.S172QPilotMultiradialImageActual
import tmp.sheaf.xif.paper.GenericQPilotCompletionPowerActual
/-! # S191: actual carrier equivalence and qPilot image-point equality
Uses the PiTensorProduct one-factor equivalence (subsingletonEquiv) to construct
the inverse of the one-factor embedding.  This gives an actual per-b linear
equivalence between the S156 completion fiber and the S172 Block, and the
two-way inverse laws, hence the image-point equality.  No inequality. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S191QPilotCarrierTransportActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.GenericQPilotCompletionPowerActual
open LeanFormal.IUT.XiFPaper.S156QPilotSideObjectActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open LeanFormal.IUT.XiFPaper.S22DependentProductActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry (l := l) T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry (l := l) T b))]
/-- The one-factor tensor family at b. -/
abbrev s191TensorFamily (b : Bad (nativePlaceSelection T)) : PUnit.{1} → Type :=
  fun _ => CommonPrimeCompletion (sourceThetaPlace T b)
/-- The actual one-factor linear equivalence. -/
noncomputable def s191BlockEquiv (b : Bad (nativePlaceSelection T)) :
    Block (G := sourceQGeometry (l := l) T b) ≃ₗ[ℚ_[qVFamTensorP T b]]
      s191TensorFamily T b () :=
  PiTensorProduct.subsingletonEquiv (s := s191TensorFamily T b)
    (i₀ := ())
/-- Inverse/coordinate map blockToFiber. -/
noncomputable def blockToFiber (b : Bad (nativePlaceSelection T)) :
    Block (G := sourceQGeometry (l := l) T b) → DependentCompletion T b :=
  fun y => (s191BlockEquiv T b y : DependentCompletion T b)
/-- Embedding map fiberToBlock. -/
noncomputable def s156FiberToBlock (b : Bad (nativePlaceSelection T)) :
    DependentCompletion T b → Block (G := sourceQGeometry (l := l) T b) :=
  fun x => (s191BlockEquiv T b).symm (x : s191TensorFamily T b ())
/-- Left inverse law. -/
theorem blockToFiber_s156FiberToBlock
    (b : Bad (nativePlaceSelection T)) (x : DependentCompletion T b) :
    blockToFiber T b (s156FiberToBlock T b x) = x :=
  (s191BlockEquiv T b).apply_symm_apply x
/-- Right inverse law. -/
theorem s156FiberToBlock_blockToFiber
    (b : Bad (nativePlaceSelection T))
    (y : Block (G := sourceQGeometry (l := l) T b)) :
    s156FiberToBlock T b (blockToFiber T b y) = y :=
  (s191BlockEquiv T b).symm_apply_apply y
/-- Product-level carrier map. -/
noncomputable def s156ProductToBlock :
    DependentCompletionProduct T → QPilotMultiradialCarrier (l := l) T :=
  fun x b => s156FiberToBlock T b (x b)
/-- The actual qVFamily q product point. -/
theorem dependentQVFamProductPoint_eq_qVFamily :
    dependentQVFamProductPoint T =
      (fun b : Bad (nativePlaceSelection T) => (qVFamily T b).q) := rfl
/-- The S172 image point equals the carrier-map image of the qVFamily q point. -/
theorem QPilotMultiradialImagePoint_eq_s156ProductToBlock :
    QPilotMultiradialImagePoint (l := l) T =
      s156ProductToBlock T (dependentQVFamProductPoint T) := by
  funext b
  let e := s191BlockEquiv T b
  have hmap :
      s156ProductToBlock T (dependentQVFamProductPoint T) b =
        e.symm ((qVFamily T b).q : s191TensorFamily T b ()) := rfl
  rw [hmap]
  apply e.injective
  rw [e.apply_symm_apply]
  change e (QPilotMultiradialImagePoint (l := l) T b) =
    (qVFamily T b).q
  unfold QPilotMultiradialImagePoint genericQPilotImagePoint
    paperQParameterImagePoint
  have hg : (gaussExponent (SignedLabelOneActual.oneLabel l).1).toNat = 1 :=
    SignedLabelOneActual.gaussExponent_oneLabel l
  simp only [sourceQGeometry, sourceQUnit, sourceQVFamilyUnit, hg, pow_one,
    Units.val_mk0]
  change (PiTensorProduct.subsingletonEquiv (s := s191TensorFamily T b)
    (i₀ := ())) ((PiTensorProduct.tprod ℚ_[qVFamTensorP T b])
      (fun _ => (qVFamily T b).q ^ 1)) = (qVFamily T b).q
  have ht := PiTensorProduct.subsingletonEquiv_apply_tprod
    (R := ℚ_[qVFamTensorP T b]) (s := s191TensorFamily T b) (i₀ := ())
    (f := fun _ => (qVFamily T b).q ^ 1)
  convert ht using 2
  exact (pow_one ((qVFamily T b).q)).symm
/-- The exact carrier equivalence object. -/
structure S191CarrierEquivActual where
  toFun : (b : Bad (nativePlaceSelection T)) →
    DependentCompletion T b → Block (G := sourceQGeometry (l := l) T b)
  invFun : (b : Bad (nativePlaceSelection T)) →
    Block (G := sourceQGeometry (l := l) T b) → DependentCompletion T b
  left_inv : ∀ (b : Bad (nativePlaceSelection T)) (x : DependentCompletion T b),
    invFun b (toFun b x) = x
  right_inv : ∀ (b : Bad (nativePlaceSelection T))
    (y : Block (G := sourceQGeometry (l := l) T b)),
    toFun b (invFun b y) = y
/-- Actual carrier equivalence inhabitant. -/
noncomputable def s191CarrierEquivActual : S191CarrierEquivActual T where
  toFun := s156FiberToBlock T
  invFun := blockToFiber T
  left_inv := blockToFiber_s156FiberToBlock T
  right_inv := s156FiberToBlock_blockToFiber T
end LeanFormal.IUT.XiFPaper.S191QPilotCarrierTransportActual
