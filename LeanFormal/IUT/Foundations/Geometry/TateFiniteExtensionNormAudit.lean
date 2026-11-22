import LeanFormal.IUT.Foundations.Geometry.TateFiniteExtensionNorm

/- Public signatures and kernel axiom dependencies only; no definition bodies. -/

#check @spectralNorm.normedField
#check @spectralNorm.normedSpace
#check @spectralNorm.normedAlgebra
#check @spectralNorm.completeSpace

open IUT.TateFiniteExtensionNorm

#check @extensionNormedField
#check @extensionNormedField_toField
#check @extensionNormedSpace
#check @extensionNormedSpace_toModule
#check @extensionNormedAlgebra
#check @extensionNormedAlgebra_toAlgebra
#check @extension_completeSpace
#check @exists_complete_ultrametric_norm_extension

#print axioms extensionNormedField
#print axioms extensionNormedField_toField
#print axioms extension_norm_eq_spectralNorm
#print axioms extension_norm_algebraMap
#print axioms extension_norm_mul
#print axioms extension_norm_add_le_max
#print axioms extension_isUltrametricDist
#print axioms extensionNormedSpace
#print axioms extensionNormedAlgebra
#print axioms extensionNormedSpace_toModule
#print axioms extensionNormedAlgebra_toAlgebra
#print axioms extension_completeSpace
#print axioms extension_norm_smul
#print axioms exists_complete_ultrametric_norm_extension
