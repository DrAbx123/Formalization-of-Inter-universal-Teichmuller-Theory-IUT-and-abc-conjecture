import tmp.sheaf.xif.paper.S2256QHomEqualizerType1IdActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2259QMapPrecompActual

universe u

variable (U V : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
variable (f : U ⟶ V)

/-- The map of the actual pointwise colimit Q is the precomposition functor
S1971PrecompFunctor.  This is definitional from the construction of Q via
S2152PFunctor.toPseudofunctor'. -/
theorem S2259QMapPrecomp :
    (S2152Q.map f).toFunctor = S1971PrecompFunctor f :=
  rfl

/-- The object-level back map of Q.map is the precomposition formula. -/
theorem S2259QMap_obj_back (P : S1971PointwiseQuotient U) :
    ((S2152Q.map f).toFunctor.obj P).back = f.as.unop ≫ P.back := by
  rw [S2259QMapPrecomp]
  exact S1971PrecompFunctor_obj_back f P

/-- The same formula for the underlying action-category object of Q. -/
theorem S2259QMap_obj_back_actual
    (P : S2152Q.obj U) :
    ((S2152Q.map f).toFunctor.obj P).back = f.as.unop ≫ P.back := by
  change ((S1971PrecompFunctor f).obj P).back = f.as.unop ≫ P.back
  exact S1971PrecompFunctor_obj_back f P

#print axioms S2259QMapPrecomp
#print axioms S2259QMap_obj_back

end LeanFormal.IUT.XiFPaper.S2259QMapPrecompActual

end
