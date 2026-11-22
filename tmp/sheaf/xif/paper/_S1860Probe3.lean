import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
open scoped TensorProduct
open LinearMap

#check @TensorProduct.lift.equiv
#check @TensorProduct.uncurry
#check @TensorProduct.mk
#check @TensorProduct.lift
#check @TensorProduct.AlgebraTensorModule.lift
#check @TensorProduct.AlgebraTensorModule.curry
#check @TensorProduct.AlgebraTensorModule.uncurry
#check @LinearMap.lcomp
#check @LinearMap.compr₂
#check @TensorProduct.comm
#check @TensorProduct.assoc
#check @TensorProduct.map
#check @LinearMap.baseChange_apply
#check @LinearMap.baseChange_comp
#check @TensorProduct.curry
