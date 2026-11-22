import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.RingTheory.IsTensorProduct

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct

#check @Algebra.TensorProduct.productMap
#check @Algebra.TensorProduct.ext'
#check @Algebra.TensorProduct.ext
#check @Algebra.TensorProduct.includeLeft
#check @Algebra.TensorProduct.includeRight
#check @AlgHom.pi
#check @Pi.evalAlgHom
#check @IsLimit.conePointUniqueUpToIso
#check @CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.mk'
#check @CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.mk'
#check @CategoryTheory.ObjectProperty.prop_of_isLimit
#check @CategoryTheory.Limits.hasLimitsOfShape_of_closedUnderLimits
#check @CategoryTheory.Limits.hasColimitsOfShape_of_closedUnderColimits
#print CategoryTheory.Limits.HasFiniteCoproducts
#check @CategoryTheory.Limits.WalkingSpan.Hom.fst
#check @CategoryTheory.Limits.PushoutCocone.IsColimit.mk
#check @CategoryTheory.Limits.PushoutCocone.isColimitAux'
#check @CategoryTheory.Limits.span
#check @CategoryTheory.Limits.Fan.mk
#check @CategoryTheory.Limits.productIsProduct
#check @Module.Finite.of_restrictScalars
#check @Module.Finite.trans
#check @Module.Finite.tensorProduct
#check @Module.Finite.base_change
#check @Module.Finite.of_surjective
#check @Algebra.Etale.of_restrictScalars
#check @Algebra.Etale.baseChange
#check @CommAlgCat.algEquivOfIso
#check @CommAlgCat.isoEquivAlgEquiv
