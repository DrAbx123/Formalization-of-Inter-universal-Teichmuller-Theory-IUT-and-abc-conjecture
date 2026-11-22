import tmp.sheaf.xif.paper.S2308EqualizerIsoFinalActual
import Mathlib.CategoryTheory.Limits.Types.Equalizers

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2308EqualizerIsoFinalActual
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

namespace LeanFormal.IUT.XiFPaper.S2312EqualizerIsoFinal2Actual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
variable (T : (Over S)ᵒᵖ)

/-- Equalizer object to explicit subtype. -/
noncomputable def S2312EqualizerSubtypeIso :
    (Limits.equalizer (S2285f S M) (S2285g S N)).obj T ≅
      {h : Iut.SignGroup // S2267fPoint S M T h = S2267gPoint S N T h} := by
  let e₁ := S2308EqualizerObjIso S M N T
  let e₂ := Limits.Types.equalizerIso ((S2285f S M).app T) ((S2285g S N).app T)
  exact e₁ ≪≫ e₂

/-- Q hom object to equalizer object at T. -/
noncomputable def S2312QHomEqualizerObjIso :
    (S2152Q.presheafHom M N).obj T ≅
      (Limits.equalizer (S2285f S M) (S2285g S N)).obj T := by
  let e₁ := eqToIso (S2271QHomObj_eq_subtype S M N T)
  let e₂ := S2312EqualizerSubtypeIso S M N T
  exact e₁ ≪≫ e₂.symm

#print axioms S2312EqualizerSubtypeIso
#print axioms S2312QHomEqualizerObjIso

end LeanFormal.IUT.XiFPaper.S2312EqualizerIsoFinal2Actual

end
