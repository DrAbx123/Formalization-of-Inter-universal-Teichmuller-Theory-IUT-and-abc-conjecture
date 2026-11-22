import tmp.sheaf.xif.paper.S2490RestrictionSectionActual
import tmp.sheaf.xif.paper.S2495cFUnconditionalActual
import tmp.sheaf.xif.paper.S2502AwayEquivActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2482QiArithmeticActual
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual

/-- The single syntactic base type for the whole unified reconstruction. -/
abbrev UB : Type := S2480QiActual.F
local instance : Field UB := inferInstance
local instance : CommRing UB := inferInstance

/-- The l=5 arithmetic data, re-stated with `UB` as carrier. -/
noncomputable def S2504A : InitialThetaArithmeticData S2482Arithmetic.l5 := S2490A

theorem S2504A_F : S2504A.F = UB := rfl
theorem S2504A_K : S2504A.K = UB := rfl

/-- Re-stated affine line over the unified base `UB` with the canonical
`algebraMap UB UB[x]` structure map. -/
noncomputable def S2504KOver : Iut.SchemeOverField UB :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap UB (MvPolynomial (Fin 1) UB))))

noncomputable def S2504FOver : Iut.SchemeOverField UB := S2504KOver

#check S2504A
#check S2504KOver
#check S2504FOver
end LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
end
