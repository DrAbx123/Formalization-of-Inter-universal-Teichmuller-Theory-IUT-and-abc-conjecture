import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.EffectiveEpi
open CategoryTheory AlgebraicGeometry
#check Scheme.fpqcTopology
#check Scheme.fpqcPrecoverage
#check Scheme.Hom.singleton_mem_fpqcPrecoverage
#check Scheme.fpqcTopology
#check (inferInstance : Scheme.fpqcTopology.Subcanonical)
#check GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
#check Presieve.IsSheafFor
#check GrothendieckTopology.Subcanonical
#check EffectiveEpi
#check EffectiveEpi.desc
#check EffectiveEpi.fac