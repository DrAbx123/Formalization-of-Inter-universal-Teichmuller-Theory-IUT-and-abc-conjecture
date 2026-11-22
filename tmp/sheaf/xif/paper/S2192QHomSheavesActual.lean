import tmp.sheaf.xif.paper.S2183QHomEqualizerIdActual
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Continuous
import tmp.sheaf.n8.closure.RepresentableStackIsStackConstructed
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual

variable (S : Iut.SchemeOverField S1726K)

/-- The exact constant-sheaf API missing for the sign group sheaf. -/
def S2192HasWeakSheafify : Prop :=
  Nonempty (HasWeakSheafify ((Iut.SchemeOverField.etaleTopology S1726K).over S) Type)

/-- The constant sign group sheaf on the slice etale site, conditional on the
constant-sheaf API. -/
noncomputable def S2192P (h : S2192HasWeakSheafify S) :
    Sheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Type) :=
  letI := h.some
  (constantSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Type)).obj Iut.SignGroup

/-- The underlying presheaf of P. -/
noncomputable abbrev S2192P_presheaf (h : S2192HasWeakSheafify S) :
    ((Over S)ᵒᵖ ⥤ Type) :=
  (S2192P S h).1

/-- The constant sign group sheaf property, conditional on the missing API. -/
theorem S2192P_isSheaf (h : S2192HasWeakSheafify S) :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S)
      (S2192P_presheaf S h) :=
  (S2192P S h).2

/-- The representable morphism presheaf T |-> Hom(T.left, S1726AffineOver) on
the slice site. -/
noncomputable def S2192R : ((Over S)ᵒᵖ ⥤ Type) :=
  (Over.forget S).op ⋙ yoneda.obj S1726AffineOver

/-- The representable morphism presheaf is a sheaf for the slice etale
topology. -/
theorem S2192R_isSheaf :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S)
      (S2192R S) := by
  have hY : Presheaf.IsSheaf (Iut.SchemeOverField.etaleTopology S1726K)
      (yoneda.obj S1726AffineOver) :=
    LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed.representableEtalePresheaf_isSheaf
      (F := S1726K) S1726AffineOver
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    ((Over.forget S).op_comp_isSheaf_of_isSheaf_type
      ((Iut.SchemeOverField.etaleTopology S1726K).over S)
      ((isSheaf_iff_isSheaf_of_type _ _).mp hY))

/-- The P/R half of the Q hom equalizer data, conditional on the constant-sheaf
API for P. -/
structure S2192HomSheaves (h : S2192HasWeakSheafify S) where
  P : ((Over S)ᵒᵖ ⥤ Type)
  R : ((Over S)ᵒᵖ ⥤ Type)
  hP : Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) P
  hR : Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) R

/-- Actual P/R package, conditional on the constant-sheaf API. -/
noncomputable def S2192HomSheaves_actual (h : S2192HasWeakSheafify S) :
    S2192HomSheaves S h where
  P := S2192P_presheaf S h
  R := S2192R S
  hP := S2192P_isSheaf S h
  hR := S2192R_isSheaf S

/-- The exact first missing for the P/R half: the constant-sheaf API for the
slice site.  R is already constructed and proved to be a sheaf. -/
def S2192FirstMissing : Prop := S2192HasWeakSheafify S

#print axioms S2192P_isSheaf
#print axioms S2192R_isSheaf
#print axioms S2192HomSheaves_actual

end LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual

end
