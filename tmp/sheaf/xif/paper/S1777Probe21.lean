import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe21

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

#check @Scheme.Spec_obj
#check @Functor.fromPUnit
#check @Functor.fromPUnit_obj
#check @CostructuredArrow.mk_left
#check @CostructuredArrow.mk_hom
#check @CostructuredArrow.mk_right

example (X : S1733Slice) : (X.hom : Scheme.Spec.obj X.left ⟶ Base) = X.hom := rfl

example (X : S1733Slice) : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) := by
  show IsAffine S1733BaseScheme
  infer_instance

example (X : S1733Slice) : IsAffine (Scheme.Spec.obj X.left) := inferInstance

end Probe21
