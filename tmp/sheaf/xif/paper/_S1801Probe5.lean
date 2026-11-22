import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans

namespace S1801Probe

variable (F : Type) [Field F]

def baseObj : LocallyDiscrete (SchemeOverField F)ᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op (Over.mk (𝟙 (Spec (CommRingCat.of F)))))

def constPseudo (C : Type) [Category C] : EtaleStackPseudofunctor F :=
  ((Functor.const (SchemeOverField F)ᵒᵖ).obj (Cat.of C)).toPseudofunctor'

@[simp] lemma constPseudo_obj (C : Type) [Category C]
    (U : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    (constPseudo F C).obj U = Cat.of C := rfl

@[simp] lemma constPseudo_map (C : Type) [Category C]
    {U V : LocallyDiscrete (SchemeOverField F)ᵒᵖ} (f : U ⟶ V) :
    (constPseudo F C).map f = 𝟙 (Cat.of C) := rfl

lemma subsingleton_hom₂_punit {C : Cat.{0, 0}} (G H : C ⟶ Cat.of (Discrete PUnit.{1})) :
    Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

lemma subsingleton_hom₂_discrete {C : Cat.{0, 0}} {A : Type}
    (G H : C ⟶ Cat.of (Discrete A)) : Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

lemma subsingleton_mod_punit {W : EtaleStackPseudofunctor F}
    (a b : W ⟶ constPseudo F (Discrete PUnit.{1})) : Subsingleton (a ⟶ b) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (subsingleton_hom₂_punit (a.app U) (b.app U)).elim _ _

lemma subsingleton_mod_discrete {W : EtaleStackPseudofunctor F} {A : Type}
    (a b : W ⟶ constPseudo F (Discrete A)) : Subsingleton (a ⟶ b) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (subsingleton_hom₂_discrete (a.app U) (b.app U)).elim _ _

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

def constZero (W : EtaleStackPseudofunctor F) :
    Pseudofunctor.StrongTrans W (constPseudo F (Discrete (Fin 2))) where
  app U := ((Functor.const (W.obj U).α).obj (Discrete.mk (0 : Fin 2))).toCatHom
  naturality {a b} f := by
    apply Cat.Hom.isoMk
    exact eqToIso rfl
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
abbrev pointStack : EtaleStackPseudofunctor F := constPseudo F (Discrete PUnit.{1})

abbrev twoStack : EtaleStackPseudofunctor F := constPseudo F (Discrete (Fin 2))

noncomputable def degenSquare :
    EtalePseudofunctorSquare (twoStack F) (pointStack F) (pointStack F) (pointStack F) where
  toX := toOne F (twoStack F)
  toY := toOne F (twoStack F)
  xToBase := Pseudofunctor.StrongTrans.id (pointStack F)
  yToBase := Pseudofunctor.StrongTrans.id (pointStack F)
  commutes := Iso.refl (Pseudofunctor.StrongTrans.vcomp (toOne F (twoStack F))
    (Pseudofunctor.StrongTrans.id (pointStack F)))

attribute [local instance] subsingleton_mod_punit subsingleton_mod_discrete

noncomputable def degenWitness : (degenSquare F).TwoPullbackWitness where
  lift W c := constZero F W
  liftToX W c := isoToOne F (Pseudofunctor.StrongTrans.vcomp (constZero F W) (degenSquare F).toX) c.toX
  liftToY W c := isoToOne F (Pseudofunctor.StrongTrans.vcomp (constZero F W) (degenSquare F).toY) c.toY
  liftTwoCell W source target m := 𝟙 (constZero F W)
  liftTwoCell_toX := by
    intro W source target m
    exact Subsingleton.elim _ _
  liftTwoCell_toY := by
    intro W source target m
    exact Subsingleton.elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    exact (subsingleton_mod_discrete (W := W) (A := Fin 2) first second).elim alpha beta

noncomputable def degenCone : (degenSquare F).Cone (twoStack F) where
  toX := Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (twoStack F)) (degenSquare F).toX
  toY := Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id (twoStack F)) (degenSquare F).toY
  commutes := isoToOne F _ _

theorem degen_not_iso :
    ¬ Nonempty (Iso (Pseudofunctor.StrongTrans.id (twoStack F)) (constZero F (twoStack F))) := by
  rintro ⟨e⟩
  have h := (e.hom.as.app (baseObj F)).toNatTrans.app (Discrete.mk (1 : Fin 2))
  have h' : (1 : Fin 2) = 0 := by simpa using Discrete.eq_of_hom h
  exact absurd h' (by decide)

/-- The S1784-style essential-surjectivity schema for an arbitrary square. -/
def essSurjOf {P X Y Z : EtaleStackPseudofunctor F} (sq : EtalePseudofunctorSquare P X Y Z)
    (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor F) (c : sq.Cone W) (f : Pseudofunctor.StrongTrans W P),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toX) c.toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toY) c.toY) →
        Nonempty (Iso f (w.lift W c))

theorem degen_essSurj_false : ¬ essSurjOf (F := F) (sq := degenSquare F) (w := degenWitness F) := by
  intro h
  apply degen_not_iso F
  exact h (twoStack F) (degenCone F) (Pseudofunctor.StrongTrans.id (twoStack F))
    ⟨Iso.refl _⟩ ⟨Iso.refl _⟩

theorem no_generic_essSurj :
    ¬ (∀ (P X Y Z : EtaleStackPseudofunctor F) (sq : EtalePseudofunctorSquare P X Y Z)
      (w : sq.TwoPullbackWitness), essSurjOf sq w) := by
  intro h
  exact degen_essSurj_false F (h _ _ _ _ (degenSquare F) (degenWitness F))

end S1801Probe