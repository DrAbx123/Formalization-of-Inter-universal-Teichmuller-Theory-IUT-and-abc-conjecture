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

namespace Probe34

#check @IsFinite.finite_app
#check @Etale.etale_appLE
#check @Scheme.Hom.appTop
#check @Scheme.Hom.appLE
#check @Scheme.Hom.appLE_top
#check @Scheme.Hom.app_top
#check @Scheme.Hom.appTop_eq_appLE

lemma appTop_finite (X : S1733Slice) : RingHom.Finite (X.hom.appTop).hom := by
  have h := (X.prop.1).finite_app ⊤ (isAffineOpen_top (Scheme.Spec.obj X.left))
  exact h

lemma appTop_etale (X : S1733Slice) : RingHom.Etale (X.hom.appTop).hom := by
  have h := (X.prop.2).etale_appLE (U := ⊤) (isAffineOpen_top _) (V := ⊤)
    (isAffineOpen_top _) le_top
  exact h

end Probe34
