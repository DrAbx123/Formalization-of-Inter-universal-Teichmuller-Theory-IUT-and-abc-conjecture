import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Algebra.Tower

open scoped TensorProduct

namespace S1797Probe

#check @Algebra.TensorProduct.instAlgebra
#check @Algebra.TensorProduct.instAlgebraOfIsScalarTower
#check @TensorProduct.smul_tmul'
#check @TensorProduct.smul_tmul
#check @TensorProduct.tmul_smul
#check @TensorProduct.tmul_smul_comm
#check @Algebra.TensorProduct.includeLeft
#check @Algebra.TensorProduct.includeRight
#check @Algebra.TensorProduct.lmul'
#check @Algebra.TensorProduct.mul
#check @Algebra.TensorProduct.map
#check @Module.finrank_tensorProduct
#check @Module.finrank_mul_finrank
#check @LinearMap.injective_iff_surjective_of_finrank_eq_finrank
#check @Module.finrank_pos
#check @Module.finrank_pos_iff
#check @Module.finrank_eq_zero
#check @Algebra.Etale.iff_exists_algEquiv_prod
#check @Algebra.Etale.baseChange
#check @Algebra.Etale.of_restrictScalars
#check @Algebra.FormallyEtale.comp
#check @Module.Finite.trans
#check @Module.Finite.baseChange
#check @Module.Finite.of_surjective
#check @AlgEquiv.piCongrRight
#check @AlgEquiv.piCongrLeft
#check @AlgEquiv.ofBijective
#check @Pi.evalAlgHom
#check @AlgHom.pi
#check @AlgHom.prod
#check @AlgEquiv.prodCongr
#check @AlgEquiv.piComm
#check @AlgEquiv.piSum
#check @Algebra.TensorProduct.comm
#check @Algebra.TensorProduct.congr
#check @Algebra.TensorProduct.piRight
#check @Algebra.TensorProduct.piLeft

end S1797Probe
