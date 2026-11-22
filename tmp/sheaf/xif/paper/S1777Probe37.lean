import Mathlib.RingTheory.Etale.Finite
import Mathlib.Algebra.Category.CommAlgCat.Basic

noncomputable section
open CategoryTheory

namespace T

example (K : Type) [Field K] : Algebra.Etale K K := by infer_instance

noncomputable def testObj (K : Type) [Field K] : CommAlgCat.FiniteEtale K :=
  letI : Algebra K K := (RingHom.id K).toAlgebra
  letI : Module.Finite K K := by
    rw [← RingHom.finite_algebraMap, RingHom.algebraMap_toAlgebra]
    infer_instance
  letI : Algebra.Etale K K := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    infer_instance
  CommAlgCat.FiniteEtale.of K K

example (K : Type) [Field K] : algebraMap K (↥(testObj K)) = RingHom.id K := by
  show algebraMap K K = RingHom.id K
  exact RingHom.algebraMap_toAlgebra _

end T
