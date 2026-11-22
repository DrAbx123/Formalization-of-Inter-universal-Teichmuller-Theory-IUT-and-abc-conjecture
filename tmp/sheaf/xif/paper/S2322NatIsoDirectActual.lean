import tmp.sheaf.xif.paper.S2312EqualizerIsoFinal2Actual
import Mathlib.CategoryTheory.Limits.Types.Equalizers

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2312EqualizerIsoFinal2Actual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2206PConstantSheafActual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2322NatIsoDirectActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
variable (T : (Over S)ᵒᵖ)

/-- Direct objectwise component: Q hom object → pointwise equalizer, using the
subtype formula and Types.equalizerIso, without the S2308 chain. -/
noncomputable def S2322Comp :
    (S2152Q.presheafHom M N).obj T ≅
      Limits.equalizer ((S2285f S M).app T) ((S2285g S N).app T) :=
  (eqToIso (S2271QHomObj_eq_subtype S M N T)).trans
    (Limits.Types.equalizerIso ((S2285f S M).app T) ((S2285g S N).app T)).symm

#print axioms S2322Comp

end LeanFormal.IUT.XiFPaper.S2322NatIsoDirectActual

end
