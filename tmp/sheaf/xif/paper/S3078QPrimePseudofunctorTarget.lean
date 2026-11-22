import tmp.sheaf.xif.paper.S3075QPrimeAssembly
import tmp.sheaf.xif.paper.S3076QPrimeNatIsoActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3078QPrimePseudofunctorTarget

abbrev S3078K : Type 1 := Iut.SchemeOverField S2994A6K

noncomputable abbrev S3078Obj
    (U : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) : Cat.{0, 1} :=
  Cat.of (S3048SignTorsorFiber U)

noncomputable abbrev S3078Map
    {U V : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)}
    (f : U ⟶ V) :
    S3078Obj U ⥤ S3078Obj V :=
  S3075PullbackFunctor f

/-- The exact Q' pseudofunctor target: covariant map on
LocallyDiscrete C^op, with mapId/mapComp as NatIso targets. -/
structure S3078QPrimePseudofunctorTarget where
  obj : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ) → Cat.{0, 1}
  obj_eq : ∀ U, obj U = S3078Obj U
  map : ∀ {U V : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)},
    (U ⟶ V) → obj U ⥤ obj V
  mapId_target :
    ∀ U, Nonempty ((map (𝟙 U)) ≅
      CategoryTheory.Functor.id (obj U))
  mapComp_target :
    ∀ {U V W} (f : U ⟶ V) (g : V ⟶ W),
      Nonempty ((map (f ≫ g)) ≅ (map f ⋙ map g))
  mapComp_assoc_target : Prop

/-- Data sufficient to fill a pseudofunctor once the NatIsos are actual. -/
structure S3078QPrimeNatIsoData where
  mapId : ∀ U,
    S3078Map (𝟙 U) ≅ CategoryTheory.Functor.id (S3078Obj U)
  mapComp : ∀ {U V W}
    (f : U ⟶ V) (g : V ⟶ W),
    S3078Map (f ≫ g) ≅ (S3078Map f ⋙ S3078Map g)

def S3078QPrimePseudofunctorTargetProp : Prop :=
  Nonempty S3078QPrimePseudofunctorTarget



/-- The unique 2-cell action: LocallyDiscrete 2-cells are equalities. -/
noncomputable def S3078Map₂
    {U V : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)}
    {f g : U ⟶ V} (η : f ⟶ g) :
    S3078Map f ⟶ S3078Map g :=
  eqToHom (congrArg S3078Map (CategoryTheory.LocallyDiscrete.eq_of_hom η))

theorem S3078Map₂_id
    {U V : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)}
    (f : U ⟶ V) :
    S3078Map₂ (𝟙 f) = 𝟙 (S3078Map f) := by
  simp [S3078Map₂]

theorem S3078Map₂_comp
    {U V : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)}
    {f g h : U ⟶ V} (η : f ⟶ g) (θ : g ⟶ h) :
    S3078Map₂ (η ≫ θ) = S3078Map₂ η ≫ S3078Map₂ θ := by
  simp only [S3078Map₂]
  rw [← eqToHom_trans]

#check S3078Map₂
#check S3078Map₂_id
#check S3078Map₂_comp



/-- Actual prelax part: obj/map/map₂ with Cat.Hom/Cat.Hom₂ conversions. -/
noncomputable def S3078PrelaxFunctor :
    PrelaxFunctor (CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) Cat.{0, 1} where
  obj := S3078Obj
  map := fun {U V} f => (S3078Map f).toCatHom
  map₂ := fun {U V} {f g} η => (S3078Map₂ (U := U) (V := V) η).toCatHom₂
  map₂_id := fun {U V} f => by
    rw [S3078Map₂_id, NatTrans.toCatHom₂_id]
    rfl
  map₂_comp := fun {U V} {f g h} η θ => by
    rw [S3078Map₂_comp, NatTrans.toCatHom₂_comp]
    rfl

/-- Actual mapId, converted from S3076MapId via Cat.Hom.isoMk. -/
noncomputable def S3078MapId
    (U : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) :
    S3078PrelaxFunctor.map (𝟙 U) ≅ 𝟙 (S3078PrelaxFunctor.obj U) :=
  Cat.Hom.isoMk (LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual.S3076MapId U)

/-- Partial pseudofunctor: all fields except mapComp and the five mapComp
coherence fields. -/
structure S3078QPrimePartialPseudofunctor where
  toPrelaxFunctor : PrelaxFunctor (CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) Cat.{0, 1}
  mapId : (U : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) →
    toPrelaxFunctor.map (𝟙 U) ≅ 𝟙 (toPrelaxFunctor.obj U)

#check S3078PrelaxFunctor
#check S3078MapId
#check S3078QPrimePartialPseudofunctor


/-- Exact remaining Pseudofunctor coherence targets, parameterized by the
prelax part, mapId and mapComp.  These are the five fields of
Pseudofunctor.mk beyond mapComp. -/
structure S3078PseudofunctorCoherenceTarget
    (P : PrelaxFunctor (CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) Cat.{0, 1})
    (mapId : (a : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) →
      P.map (𝟙 a) ≅ 𝟙 (P.obj a))
    (mapComp : {a b c : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)} →
      (f : a ⟶ b) → (g : b ⟶ c) →
        P.map (f ≫ g) ≅ P.map f ≫ P.map g) where
  map₂_whisker_left :
    ∀ {a b c : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)}
      (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      P.map₂ (Bicategory.whiskerLeft f η) =
        (mapComp f g).hom ≫
          Bicategory.whiskerLeft (P.map f) (P.map₂ η) ≫
            (mapComp f h).inv
  map₂_whisker_right :
    ∀ {a b c : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)}
      {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      P.map₂ (Bicategory.whiskerRight η h) =
        (mapComp f h).hom ≫
          Bicategory.whiskerRight (P.map₂ η) (P.map h) ≫
            (mapComp g h).inv
  map₂_associator :
    ∀ {a b c d : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)}
      (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      P.map₂ (Bicategory.associator f g h).hom =
        (mapComp (f ≫ g) h).hom ≫
          Bicategory.whiskerRight (mapComp f g).hom (P.map h) ≫
            (Bicategory.associator (P.map f) (P.map g) (P.map h)).hom ≫
              Bicategory.whiskerLeft (P.map f) (mapComp g h).inv ≫
                (mapComp f (g ≫ h)).inv
  map₂_left_unitor :
    ∀ {a b : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)} (f : a ⟶ b),
      P.map₂ (Bicategory.leftUnitor f).hom =
        (mapComp (𝟙 a) f).hom ≫
          Bicategory.whiskerRight (mapId a).hom (P.map f) ≫
            (Bicategory.leftUnitor (P.map f)).hom
  map₂_right_unitor :
    ∀ {a b : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)} (f : a ⟶ b),
      P.map₂ (Bicategory.rightUnitor f).hom =
        (mapComp f (𝟙 b)).hom ≫
          Bicategory.whiskerLeft (P.map f) (mapId b).hom ≫
            (Bicategory.rightUnitor (P.map f)).hom

/-- The exact mapComp target, stated separately for the coherence target. -/
def S3078MapCompTarget
    (P : PrelaxFunctor (CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) Cat.{0, 1}) : Prop :=
  Nonempty ({a b c : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)} →
    (f : a ⟶ b) → (g : b ⟶ c) →
      P.map (f ≫ g) ≅ P.map f ≫ P.map g)

#check S3078PseudofunctorCoherenceTarget
#check S3078MapCompTarget


/-- Exact Pseudofunctor.mk assembly template: everything except the mapComp
value itself; mapComp plus the five coherence proofs are supplied as
arguments. -/
noncomputable def S3078PseudofunctorAssemblyTemplate
    (P : PrelaxFunctor (CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) Cat.{0, 1})
    (mapId : (a : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) →
      P.map (𝟙 a) ≅ 𝟙 (P.obj a))
    (mapComp : {a b c : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)} →
      (f : a ⟶ b) → (g : b ⟶ c) →
        P.map (f ≫ g) ≅ P.map f ≫ P.map g)
    (C : S3078PseudofunctorCoherenceTarget P mapId mapComp) :
    Pseudofunctor (CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) Cat.{0, 1} :=
  Pseudofunctor.mk P mapId mapComp
    C.map₂_whisker_left
    C.map₂_whisker_right
    C.map₂_associator
    C.map₂_left_unitor
    C.map₂_right_unitor

#check S3078PseudofunctorAssemblyTemplate

#check S3078Obj
#check S3078Map
#check S3078QPrimePseudofunctorTarget
#check S3078QPrimeNatIsoData
#check S3078QPrimePseudofunctorTargetProp

end LeanFormal.IUT.XiFPaper.S3078QPrimePseudofunctorTarget
end
