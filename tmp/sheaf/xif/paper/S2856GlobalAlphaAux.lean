import tmp.sheaf.xif.paper.S2855StackAutoSquareActual
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual
import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2854StackAutoFromSchemeActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2851A6D6GeometryActual
open LeanFormal.IUT.XiFPaper.S2855StackAutoSquareActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2856GlobalAlphaAux

local instance : Field K := inferInstance
local instance : DecidableEq K := Classical.decEq _

/-- Exact global-alpha data missing from S2853: a self-map of the glued
projective scheme whose square is the identity. -/
structure S2856GlobalAlpha where
  alpha : S2844X ⟶ S2844X
  alpha_square : alpha ≫ alpha = 𝟙 S2844X

/-- The actual stack square from the global-alpha data. -/
noncomputable def S2856StackAuto_square (A : S2856GlobalAlpha) :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp
        (S2854StackAuto A.alpha) (S2854StackAuto A.alpha))
      (Iut.HyperbolicOrbicurve.Hom.id S2851HyperbolicOrbicurve) :=
  S2855StackAuto_square A.alpha A.alpha_square

/-! S2853 chart-Z endo is only affine-chart, not global. -/
#check S2853ChartZSchemeEndo

#check S2856GlobalAlpha
#check S2856StackAuto_square
#print axioms S2856StackAuto_square

end LeanFormal.IUT.XiFPaper.S2856GlobalAlphaAux
end