import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe28

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

#check @Quiver.Hom.unop_op
#check @Quiver.Hom.op_unop
#check @Opposite.op_unop
#check @Opposite.unop_op
#check @Quiver.Hom.op

example (X : S1733Slice) (f : X.left ⟶ X.left) : f.unop.op = f := by
  exact Quiver.Hom.unop_op f

end Probe28
