import Mathlib.RingTheory.Etale.Finite
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1769Probe

variable (K : Type) [Field K]

def ambientBC : CommAlgCat.{0} K ⥤ CommAlgCat.{0} (AlgebraicClosure K) where
  obj A := CommAlgCat.of (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] (A : Type))
  map {A B} f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (AlgebraicClosure K) (AlgebraicClosure K)) f.hom)

def bcUnder : CommRingCat.Under (CommRingCat.of K) ⥤ CommRingCat.Under (CommRingCat.of K) :=
  CommRingCat.Under.tensorProd (CommRingCat.of K) (CommRingCat.of (AlgebraicClosure K))

def conjugated : CommAlgCat.{0} K ⥤ CommAlgCat.{0} (AlgebraicClosure K) :=
  (CommAlgCat.commAlgCatEquivUnder (CommRingCat.of K)).functor ⋙
    CommRingCat.Under.tensorProd (CommRingCat.of K) (CommRingCat.of (AlgebraicClosure K)) ⋙
    (CommAlgCat.commAlgCatEquivUnder (CommRingCat.of (AlgebraicClosure K))).inverse

example : conjugated K = ambientBC K := rfl

end S1769Probe