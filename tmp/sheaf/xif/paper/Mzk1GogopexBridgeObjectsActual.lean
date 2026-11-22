/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.AlgorithmicBridge

/-! # A515: O4 bridge object (Gogopex CommonTargetBoundBridge consumers) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexBridge

open Iut RealLineCopy

universe u

variable {source target : Copy} {index : Type u}

/-- The O4 object: an algorithmic output with a measured common-target-bound bridge.
This is the abstract home of the `3.11 => 3.11.5` step, parameterized by an actual
`AlgorithmicOutput`, an actual `RegionMeasure`, and a real bound. -/
structure BridgeObject (output : AlgorithmicOutput source target index)
    (measure : RegionMeasure target) (bound : Real) where
  /-- The source-specific bridge consuming certification. -/
  bridge : CommonTargetBoundBridge output measure bound

variable {output : AlgorithmicOutput source target index}
variable {measure : RegionMeasure target} {bound : Real}

/-- The bridge object preserves the IPL property (consumer of Gogopex). -/
theorem BridgeObject.preserves_hasIPL (B : BridgeObject output measure bound)
    (certified : output.Certified) : output.HasIPL :=
  B.bridge.preserves_hasIPL certified

/-- The bridge object preserves the SHE property (consumer of Gogopex). -/
theorem BridgeObject.preserves_hasSHE (B : BridgeObject output measure bound)
    (certified : output.Certified) : output.HasSHE :=
  B.bridge.preserves_hasSHE certified

/-- The bridge object preserves the APT property (consumer of Gogopex). -/
theorem BridgeObject.preserves_hasAPT (B : BridgeObject output measure bound)
    (certified : output.Certified) : output.HasAPT :=
  B.bridge.preserves_hasAPT certified

/-- Every comparison of the output has target volume at most the common bound. -/
theorem BridgeObject.targetVolume_le (B : BridgeObject output measure bound)
    (certified : output.Certified) (choice : index) :
    RegionMeasure.targetVolume measure (output.comparison choice) ≤ bound :=
  B.bridge.choice_targetVolume_le certified choice

/-- All target volumes are at most the common bound. -/
theorem BridgeObject.allTargetsAtMost (B : BridgeObject output measure bound)
    (certified : output.Certified) :
    RegionComparisonFamily.AllTargetsAtMost measure output.comparisons bound :=
  B.bridge.allTargetsAtMost certified

end LeanFormal.IUT.Objects.GogopexBridge
