/-
S1801 probe 2: constant pseudofunctors and thinness.
-/
import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans

namespace S1801Probe

variable (F : Type) [Field F]

/-- A base object: Spec F with its identity structure map. -/
def baseObj : LocallyDiscrete (SchemeOverField F)ᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op (Over.mk (𝟙 (Spec (CommRingCat.of F)))))

/-- The constant pseudofunctor at a category. -/
def constPseudo (C : Type) [Category C] : EtaleStackPseudofunctor F :=
  ((Functor.const (SchemeOverField F)ᵒᵖ).obj (Cat.of C)).toPseudofunctor'

/-- Its value. -/
@[simp] lemma constPseudo_obj (C : Type) [Category C]
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    (constPseudo F C).obj U = Cat.of C := rfl

/-- Its map. -/
@[simp] lemma constPseudo_map (C : Type) [Category C]
    {U V : LocallyDiscrete (SchemeOverField F)ᵒᵖ} (f : U ⟶ V) :
    (constPseudo F C).map f = 𝟙 (Cat.of C) := rfl

/-- Two-cells in Cat between functors into Discrete PUnit are unique. -/
lemma subsingleton_hom₂_punit {C : Cat.{0, 0}} (G H : C ⟶ Cat.of (Discrete PUnit.{1})) :
    Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  exact Subsingleton.elim _ _

/-- The canonical strong transformation into the constant pseudofunctor at the point. -/
def toOne (W : EtaleStackPseudofunctor F) :
    Pseudofunctor.StrongTrans W (constPseudo F (Discrete PUnit.{1})) where
  app U := (Functor.star (W.obj U).α).toCatHom
  naturality {a b} f := by
    apply Cat.Hom.isoMk
    exact Functor.punitExt _ _
  naturality_naturality := by
    intro a b f g eta
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    exact Subsingleton.elim _ _

#check toOne

end S1801Probe
