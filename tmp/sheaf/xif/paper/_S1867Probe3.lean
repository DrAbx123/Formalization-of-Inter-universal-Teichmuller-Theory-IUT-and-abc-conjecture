import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.CategoryTheory.Galois.Basic
open CategoryTheory CategoryTheory.Limits
#check @SingleObj
#check SingleObj
#check (inferInstance : Category (SingleObj (Fin 3)))
#check (inferInstance : Category (SingleObj (Type)))
#check @CategoryTheory.SingleObj.category
#check @CategoryTheory.SingleObj.toEnd
#check @PreGaloisCategory.hasQuotientsByFiniteGroups
#check @CategoryTheory.Limits.HasColimitsOfShape
