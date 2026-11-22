import tmp.sheaf.xif.paper.S3127FreeQuotientActual
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Ring.Action.Basic
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127GammaActionActual
variable {G : Type} [Group G]

noncomputable def gammaAut {Y : Scheme} (e : Y ≅ Y) :
    Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y) :=
  (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv

#check gammaAut
end LeanFormal.IUT.XiFPaper.S3127GammaActionActual
end
