import tmp.sheaf.xif.paper.S3133ExistingModelAdaptationActual
import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank

noncomputable section
open scoped NNReal ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3133ExistingModelAdaptationActual

namespace LeanFormal.IUT.XiFPaper.S3135TreeModelBaseUnitScalingActual

/-- **Fill qpilot's nontrivial procession-scaling interface**
`S3133TreeModelBaseUnitScaling` with the unconditional witness `baseUnit = -1`
(a genuine `Q_5` unit of norm one).  This is the abc-side filling of
`INDEX.MODEL.stage4-unit-map-baseunit` (prior art: the structure is defined in
S3133ExistingModelAdaptationActual:118-120; the Fact-prime-5 instance used for
`Q_[5]` is RationalCommonPrimeFinrank:22 fact_prime_five). -/
noncomputable def s3135_treeModelBaseUnitScaling : S3133TreeModelBaseUnitScaling where
  baseUnit := ⟨(-1 : ℚ_[5]), (-1 : ℚ_[5]), by ring, by ring⟩
  baseUnit_norm_one := by
    show ‖(-1 : ℚ_[5])‖ = 1
    rw [norm_neg, norm_one]

/-- The filled base unit is exactly `-1` (definitional). -/
theorem s3135_treeModelBaseUnitScaling_baseUnit :
    (s3135_treeModelBaseUnitScaling.baseUnit : ℚ_[5]) = -1 :=
  rfl

/-- The filled base unit is nontrivial. -/
theorem s3135_treeModelBaseUnitScaling_nontrivial :
    (s3135_treeModelBaseUnitScaling.baseUnit : ℚ_[5]) ≠ 1 := by
  rw [s3135_treeModelBaseUnitScaling_baseUnit]
  norm_num

#check s3135_treeModelBaseUnitScaling
#check s3135_treeModelBaseUnitScaling_baseUnit
#check s3135_treeModelBaseUnitScaling_nontrivial
end LeanFormal.IUT.XiFPaper.S3135TreeModelBaseUnitScalingActual
end
