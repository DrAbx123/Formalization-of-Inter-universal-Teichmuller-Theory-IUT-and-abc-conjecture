/-
S1801 probe 3: infrastructure for the degenerate counterexample.
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

@[simp] lemma constPseudo_obj (C : Type) [Category C]
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    (constPseudo F C).obj U = Cat.of C := rfl

@[simp] lemma constPseudo_map (C : Type) [Category C]
    {U V : LocallyDiscrete (SchemeOverField F)ᵒᵖ} (f : U ⟶ V) :
    (constPseudo F C).map f = 𝟙 (Cat.of C) := rfl

/-- Two-cells in Cat between functors into the point category are unique. -/
lemma subsingleton_hom₂_punit {C : Cat.{0, 0}} (G H : C ⟶ Cat.of (Discrete PUnit.{1})) :
    Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- Two-cells in Cat between functors into a discrete category are unique. -/
lemma subsingleton_hom₂_discrete {C : Cat.{0, 0}} {A : Type}
    (G H : C ⟶ Cat.of (Discrete A)) : Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- Modifications between strong transformations into the point are unique. -/
lemma subsingleton_mod_punit {W : EtaleStackPseudofunctor F}
    (a b : W ⟶ constPseudo F (Discrete PUnit.{1})) : Subsingleton (a ⟶ b) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (subsingleton_hom₂_punit (a.app U) (b.app U)).elim _ _

/-- Modifications between strong transformations into a discrete stack are unique. -/
lemma subsingleton_mod_discrete {W : EtaleStackPseudofunctor F} {A : Type}
    (a b : W ⟶ constPseudo F (Discrete A)) : Subsingleton (a ⟶ b) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (subsingleton_hom₂_discrete (a.app U) (b.app U)).elim _ _

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
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _

/-- Any two strong transformations into the point are 2-isomorphic. -/
noncomputable def isoToOne {W : EtaleStackPseudofunctor F}
    (a b : W ⟶ constPseudo F (Discrete PUnit.{1})) : a ≅ b :=
  Pseudofunctor.StrongTrans.isoMk
    (fun U => Cat.Hom.isoMk (Functor.punitExt (a.app U).toFunctor (b.app U).toFunctor))
    (by
      intro x y f
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext X
      apply ULift.ext
      exact Subsingleton.elim _ _)

/-- The constant-at-zero strong transformation into the two-point constant stack. -/
def constZero (W : EtaleStackPseudofunctor F) :
    Pseudofunctor.StrongTrans W (constPseudo F (Discrete (Fin 2))) where
  app U := ((Functor.const (W.obj U).α).obj (Discrete.mk (0 : Fin 2))).toCatHom
  naturality {a b} f := by
    apply Cat.Hom.isoMk
    exact eqToIso (Functor.ext (fun X => rfl) (fun X Y g => Subsingleton.elim _ _))
  naturality_naturality := by
    intro a b f g eta
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _

#check isoToOne
#check constZero

end S1801Probe
