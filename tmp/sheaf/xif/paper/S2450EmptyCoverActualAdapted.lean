import tmp.sheaf.xif.paper.S2134D9DescentActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2450EmptyCoverActualAdapted

universe v u v' u'
variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
variable {S : C}

/-- The empty presieve has empty index category. -/
instance S2450_empty_category_isEmpty :
    IsEmpty (⊥ : Presieve S).category where
  false x := x.property

/-- Descent data for the empty family is a subsingleton. -/
instance S2450_empty_descentData_subsingleton :
    Subsingleton (F.DescentData (fun (g : (⊥ : Presieve S).category) => g.obj.hom)) where
  allEq D₁ D₂ := by
    cases D₁
    cases D₂
    congr

/-- Any object of the fibre gives an amalgam for the empty-cover descent datum. -/
noncomputable def S2450_emptyAmalgam
    (M : F.obj (.mk (Opposite.op S)))
    (D : F.DescentData (fun (g : (⊥ : Presieve S).category) => g.obj.hom)) :
    Amalgam F (fun (g : (⊥ : Presieve S).category) => g.obj.hom) D where
  M := M
  iso := eqToIso (Subsingleton.elim _ D)

/-- Empty-cover effective descent, actual for every pseudofunctor F. -/
theorem S2450_empty_effDescent :
    HasEffectiveDescentPresieve F (⊥ : Presieve S) := by
  intro D
  exact ⟨F.obj (.mk (Opposite.op S)), ⟨S2450_emptyAmalgam F _ D⟩⟩

#print axioms S2450_empty_category_isEmpty
#print axioms S2450_empty_descentData_subsingleton
#print axioms S2450_empty_effDescent

end LeanFormal.IUT.XiFPaper.S2450EmptyCoverActualAdapted

end
