/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.RingTheory.IsTensorProduct

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

#check @CategoryTheory.Limits.Fan.IsLimit.mk
#check @CategoryTheory.Limits.HasLimit.isoOfNatIso
#check @CategoryTheory.Limits.hasLimit_of_iso
#check @CategoryTheory.Limits.Fan
#check @CategoryTheory.Discrete.natIsoFunctor
#check @CategoryTheory.Limits.Fan.proj
#check @CategoryTheory.Limits.Cone.postcompose
#check @CategoryTheory.Limits.IsLimit.postcomposeHomEquiv
#check @CategoryTheory.Limits.IsLimit.postcomposeInvEquiv
#check @CategoryTheory.Limits.diagramIsoSpan
#check @CategoryTheory.Limits.IsColimit.precomposeHomEquiv
#check @CategoryTheory.Limits.IsColimit.precomposeInvEquiv
#check @CategoryTheory.Limits.HasColimit.isoOfNatIso
#check @CategoryTheory.Limits.Cofan
#check @CategoryTheory.Limits.Cofan.IsColimit.mk
#check @CategoryTheory.Limits.WalkingSpan
#check @CategoryTheory.Limits.WalkingSpan.left
#check @CategoryTheory.Limits.WalkingSpan.zero
#check @CategoryTheory.Limits.WalkingSpan.right
#check @CategoryTheory.Limits.WalkingSpan.Hom.snd
#check @Algebra.pushoutDesc
#check @Algebra.IsPushout.algHom_ext
#check @Algebra.IsPushout.equiv
#check @CategoryTheory.Limits.PushoutCocone.condition
#check @CategoryTheory.Limits.PushoutCocone.inl
#check @CategoryTheory.Limits.PushoutCocone.mk
#check @CategoryTheory.Limits.PushoutCocone.IsColimit.mk
#check @AlgHom.restrictScalars
#check @IsScalarTower.of_algebraMap_eq'
#check @IsScalarTower.of_algebraMap_eq
#check @RingHom.toAlgebra
#check @Algebra.TensorProduct.includeLeft
#check @Algebra.TensorProduct.includeRight
#check @Algebra.TensorProduct.includeLeft_apply
#check @Algebra.TensorProduct.includeRight_apply
