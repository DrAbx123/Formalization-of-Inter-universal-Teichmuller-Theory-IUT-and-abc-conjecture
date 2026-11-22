import Mathlib.Logic.Small.Basic
import Mathlib.CategoryTheory.Category.ULift
open CategoryTheory
universe u v w

#check @Shrink
#check @Small
#check @small_iff
#check @Shrink.shrink

-- AsSmall: does it lower the object universe?
#check @CategoryTheory.AsSmall
#check @CategoryTheory.AsSmall.equiv
#check @CategoryTheory.SmallCategory
