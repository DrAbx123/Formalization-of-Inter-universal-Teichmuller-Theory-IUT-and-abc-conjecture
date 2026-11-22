import tmp.sheaf.xif.paper.S3128PrincipalCoverCompatActual
import Mathlib.RingTheory.Ideal.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128FiniteSpanCoverActual

/-- A finite family of elements spanning the unit ideal, giving a finite
principal affine open cover of Spec A. -/
structure S3128FiniteSpanCover (A : Type) [CommRing A] where
  ι : Type
  fintype : Fintype ι
  f : ι → A
  span_top : Ideal.span (Set.range f) = ⊤

attribute [instance] S3128FiniteSpanCover.fintype

/-- The trivial one-chart cover by f = 1. -/
noncomputable def S3128FiniteSpanCover.one (A : Type) [CommRing A] :
    S3128FiniteSpanCover A where
  ι := PUnit
  fintype := inferInstance
  f := fun _ => 1
  span_top := by
    rw [Set.range_const]
    simp

#check S3128FiniteSpanCover
#check S3128FiniteSpanCover.one

end LeanFormal.IUT.XiFPaper.S3128FiniteSpanCoverActual
end