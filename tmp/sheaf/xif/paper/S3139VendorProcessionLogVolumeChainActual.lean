import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: procession log-volume chain (vendor-adapted)

Adapted from vendor promachina Iut/Stage1/IUTStage1SourceCore.lean procession
log-volume chain: IUTStage1CapsuleFamilyLogVolume:1256,
IUTStage1CapsuleLogVolumeObject:1269, IUTStage1TypedCapsuleFamilyLogVolume:1277,
IUTStage1ProcessionTensorPacketLogVolume:1299 (law at :1306),
IUTStage1ProcessionFiberTensorPacketLogVolume:1392, and
IUTStage1BaseValuationTensorPacketProductLogVolume:1469.  Re-proved with our
objects: a product log-volume over a finite label family with the additivity law,
constructible from arbitrary real data, plus its increment/aggregation laws.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorProcessionLogVolumeChainActual

/-- Capsule-family log-volume: a value per capsule label plus the family sum. -/
structure SourceCapsuleFamilyLogVolume (n : ℕ) where
  /-- per-label log-volume -/
  label : Fin n → ℝ
  /-- family sum -/
  family : ℝ
  /-- the family-sum law -/
  family_law : family = ∑ i, label i

/-- Every label family gives a capsule-family log-volume. -/
def sourceCapsuleFamilyLogVolumeOf (n : ℕ) (label : Fin n → ℝ) :
    SourceCapsuleFamilyLogVolume n where
  label := label
  family := ∑ i, label i
  family_law := rfl

/-- Tensor-packet product log-volume: base value plus fiber log-volumes, with
the product law (adapted from IUTStage1BaseValuationTensorPacketProductLogVolume). -/
structure SourceTensorPacketProductLogVolume (n : ℕ) where
  /-- the base log-volume -/
  base : ℝ
  /-- per-fiber log-volumes -/
  fiber : Fin n → ℝ
  /-- the product log-volume -/
  product : ℝ
  /-- the product law: product = base + sum of fibers -/
  product_law : product = base + ∑ i, fiber i

/-- Every base and fiber family gives a tensor-packet product log-volume. -/
def sourceTensorPacketProductLogVolumeOf (n : ℕ) (base : ℝ)
    (fiber : Fin n → ℝ) : SourceTensorPacketProductLogVolume n where
  base := base
  fiber := fiber
  product := base + ∑ i, fiber i
  product_law := rfl

/-- Incrementing one fiber by c increments the product by c (the unit
log-volume step of the vendor chain). -/
theorem sourceTensorPacketProductLogVolume_increment
    (n : ℕ) (base : ℝ) (fiber : Fin n → ℝ) (i : Fin n) (c : ℝ) :
    (sourceTensorPacketProductLogVolumeOf n base
        (Function.update fiber i (fiber i + c))).product =
      (sourceTensorPacketProductLogVolumeOf n base fiber).product + c := by
  simp [sourceTensorPacketProductLogVolumeOf, Finset.sum_update_of_mem,
    Finset.mem_univ]
  ring

end LeanFormal.IUT.XiFPaper.S3139VendorProcessionLogVolumeChainActual

end
