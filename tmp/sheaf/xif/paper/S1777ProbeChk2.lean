import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Chk2

example : IsAffine S1733BaseScheme := inferInstance

example (X : S1733Slice) : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) := by
  haveI hbase : IsAffine S1733BaseScheme := inferInstance
  exact hbase

example (X : S1733Slice) : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) := by
  show IsAffine S1733BaseScheme
  infer_instance

example (X : S1733Slice) : RingHom.Finite (X.hom.appTop).hom := by
  haveI hbase : IsAffine S1733BaseScheme := inferInstance
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) := hbase
  exact (X.prop.1).finite_app ⊤ (isAffineOpen_top _)

end Chk2
