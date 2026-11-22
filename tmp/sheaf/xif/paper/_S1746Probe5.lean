import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Etale.Descent
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic

noncomputable section
open scoped TensorProduct
open CategoryTheory

namespace S1746Probe
universe u v w

-- (lemmas omitted for brevity; assume imported)
-- We re-declare minimal versions by importing the probe?

variable {K : Type u} [Field K] {G : Type u} [Group G]

def fixedSubalgebraOfFunctor
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)^op) :
    Subalgebra K ((F.obj (SingleObj.star G)).unop) :=
  fixedSubalgebra (K := K) (G := G) (X := (F.obj (SingleObj.star G)).unop)
    (fun g : G => (F.map (g : SingleObj.star G ⟶ SingleObj.star G)).unop.hom)

end S1746Probe
