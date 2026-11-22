import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.RingTheory.IsTensorProduct

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1745

variable (K : Type) [Field K]

section Test
variable {A B C : CommAlgCat.{0} K} (f : A ⟶ B) (g : A ⟶ C)

-- instance test 1: SMulCommClass
example : letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
    letI : IsScalarTower K (A : Type) (B : Type) :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
    SMulCommClass (A : Type) K (B : Type) := inferInstance

-- instance test 2: Algebra K of the tensor
example : letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
    letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
    letI : IsScalarTower K (A : Type) (B : Type) :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
    letI : IsScalarTower K (A : Type) (C : Type) :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
    Algebra K ((B : Type) ⊗[A] (C : Type)) := inferInstance

-- instance test 3: IsScalarTower K A tensor
example : letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
    letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
    letI : IsScalarTower K (A : Type) (B : Type) :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
    letI : IsScalarTower K (A : Type) (C : Type) :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
    IsScalarTower K (A : Type) ((B : Type) ⊗[A] (C : Type)) := inferInstance

-- instance test 4: IsScalarTower K B tensor
example : letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
    letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
    letI : IsScalarTower K (A : Type) (B : Type) :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
    letI : IsScalarTower K (A : Type) (C : Type) :=
      IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
    IsScalarTower K (B : Type) ((B : Type) ⊗[A] (C : Type)) := inferInstance

-- instance test 5: Algebra.IsPushout
example : letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
    letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
    Algebra.IsPushout (A : Type) (B : Type) (C : Type) ((B : Type) ⊗[A] (C : Type)) :=
  inferInstance

-- instance test 6: Algebra C tensor
example : letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
    letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
    Algebra (C : Type) ((B : Type) ⊗[A] (C : Type)) := inferInstance

-- instance test 7: IsScalarTower A C tensor
example : letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
    letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
    IsScalarTower (A : Type) (C : Type) ((B : Type) ⊗[A] (C : Type)) := inferInstance

end Test

end S1745
