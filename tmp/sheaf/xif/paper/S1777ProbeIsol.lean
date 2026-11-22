import Mathlib.RingTheory.Etale.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry

namespace Isol

abbrev FE : MorphismProperty Scheme.{0} := @IsFinite ⊓ @Etale
abbrev Base (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)
abbrev Slice (R : Type) [CommRing R] : Type 1 := FE.CostructuredArrow ⊤ Scheme.Spec (Base R)

variable {R : Type} [CommRing R]

example (X : Slice R) : IsAffine (Base R) := inferInstance

example (X : Slice R) : IsAffine ((Functor.fromPUnit (Base R)).obj X.right) := by
  haveI hbase : IsAffine (Base R) := inferInstance
  exact hbase

example (X : Slice R) : True := by
  haveI hbase : IsAffine (Base R) := inferInstance
  haveI : IsAffine ((Functor.fromPUnit (Base R)).obj X.right) := hbase
  trivial

lemma appTop_finite (X : Slice R) : RingHom.Finite (X.hom.appTop).hom := by
  haveI hbase : IsAffine (Base R) := inferInstance
  haveI : IsAffine ((Functor.fromPUnit (Base R)).obj X.right) := hbase
  exact (X.prop.1).finite_app ⊤ (isAffineOpen_top _)

lemma appTop_etale (X : Slice R) : RingHom.Etale (X.hom.appTop).hom := by
  haveI hbase : IsAffine (Base R) := inferInstance
  haveI : IsAffine ((Functor.fromPUnit (Base R)).obj X.right) := hbase
  exact (X.prop.2).etale_appLE (U := ⊤) (isAffineOpen_top _) (V := ⊤) (isAffineOpen_top _) le_top

end Isol
