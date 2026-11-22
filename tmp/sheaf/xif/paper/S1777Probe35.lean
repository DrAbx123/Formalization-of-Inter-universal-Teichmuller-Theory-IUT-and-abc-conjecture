import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe35

#print Scheme.Hom.appTop
#print Scheme.Hom.appLE

example (X : S1733Slice) : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) :=
  inferInstanceAs (IsAffine S1733BaseScheme)

lemma appTop_finite (X : S1733Slice) : RingHom.Finite (X.hom.appTop).hom := by
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) :=
    inferInstanceAs (IsAffine S1733BaseScheme)
  have h := (X.prop.1).finite_app ⊤ (isAffineOpen_top _)
  exact h

lemma appTop_etale (X : S1733Slice) : RingHom.Etale (X.hom.appTop).hom := by
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) :=
    inferInstanceAs (IsAffine S1733BaseScheme)
  have h := (X.prop.2).etale_appLE (U := ⊤) (isAffineOpen_top _) (V := ⊤)
    (isAffineOpen_top _) le_top
  exact h

end Probe35
