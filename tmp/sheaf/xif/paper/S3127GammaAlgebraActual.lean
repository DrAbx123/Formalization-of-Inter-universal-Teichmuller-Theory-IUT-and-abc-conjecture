import tmp.sheaf.xif.paper.S3127GammaCompActual
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127GammaAlgebraActual
variable {K : Type} [Field K]

noncomputable def gammaAlgebraMap (Y : SchemeOverField K) :
    K →+* Scheme.Γ.obj (Opposite.op Y.left) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Scheme.Γ.map Y.hom.op).hom

noncomputable instance gammaAlgebra (Y : SchemeOverField K) :
    Algebra K (Scheme.Γ.obj (Opposite.op Y.left)) :=
  (gammaAlgebraMap Y).toAlgebra

#check gammaAlgebraMap
#check gammaAlgebra
end LeanFormal.IUT.XiFPaper.S3127GammaAlgebraActual
end
