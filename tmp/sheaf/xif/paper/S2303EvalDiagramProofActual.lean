import tmp.sheaf.xif.paper.S2285RMapNatActual
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2206PConstantSheafActual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2303EvalDiagramProofActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
variable (T : (Over S)ᵒᵖ)

abbrev S2303F : WalkingParallelPair ⥤ ((Over S)ᵒᵖ ⥤ Type) :=
  Limits.parallelPair (S2285f S M) (S2285g S N)

abbrev S2303G : WalkingParallelPair ⥤ Type :=
  Limits.parallelPair ((S2285f S M).app T) ((S2285g S N).app T)

theorem S2303_obj_zero :
    (S2303F S M N ⋙ (evaluation (Over S)ᵒᵖ Type).obj T).obj WalkingParallelPair.zero =
      (S2206P0 S).obj T :=
  rfl

theorem S2303_obj_one :
    (S2303F S M N ⋙ (evaluation (Over S)ᵒᵖ Type).obj T).obj WalkingParallelPair.one =
      (S2192R S).obj T :=
  rfl

theorem S2303_map_left :
    (S2303F S M N ⋙ (evaluation (Over S)ᵒᵖ Type).obj T).map WalkingParallelPairHom.left =
      (S2285f S M).app T :=
  rfl

theorem S2303_map_right :
    (S2303F S M N ⋙ (evaluation (Over S)ᵒᵖ Type).obj T).map WalkingParallelPairHom.right =
      (S2285g S N).app T :=
  rfl

#print axioms S2303_obj_zero
#print axioms S2303_obj_one
#print axioms S2303_map_left
#print axioms S2303_map_right

noncomputable def S2303EvalDiagramIso :
    S2303F S M N ⋙ (evaluation (Over S)ᵒᵖ Type).obj T ≅
      S2303G S M N T :=
  Limits.parallelPair.ext
    (eqToIso (S2303_obj_zero S M N T))
    (eqToIso (S2303_obj_one S M N T))
    (by simp [S2303_map_left, eqToIso])
    (by simp [S2303_map_right, eqToIso])

#print axioms S2303EvalDiagramIso

end LeanFormal.IUT.XiFPaper.S2303EvalDiagramProofActual

end
