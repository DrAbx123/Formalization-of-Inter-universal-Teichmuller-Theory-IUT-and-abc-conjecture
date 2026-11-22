import tmp.sheaf.xif.paper.S3076QPrimeIsStack

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3076QPrimeIsStack
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3077QPrimeCoherence

/-- Component/naturality data for a natural isomorphism between pullback
functors on the torsor fiber. -/
structure S3077NatIsoData
    {U V : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ)}
    (F G : S3048SignTorsorFiber U ⥤ S3048SignTorsorFiber V) where
  component :
    ∀ P : S3048SignTorsorFiber U,
      S3049TorsorIso V (F.obj P) (G.obj P)
  naturality : Prop

/-- Target: pullback along the identity is naturally isomorphic to the
identity functor. -/
def S3077MapIdTarget
    (U : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ)) : Prop :=
  Nonempty (S3077NatIsoData
    (S3075PullbackFunctor (𝟙 U))
    (CategoryTheory.Functor.id (S3048SignTorsorFiber U)))

/-- Target: pullback along a composite is naturally isomorphic to the
composite of pullback functors. -/
def S3077MapCompTarget
    {U V W : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ)}
    (f : U ⟶ V) (g : V ⟶ W) : Prop :=
  Nonempty (S3077NatIsoData
    (S3075PullbackFunctor (f ≫ g))
    (S3075PullbackFunctor f ⋙ S3075PullbackFunctor g))

/-- The full pseudofunctor coherence target. -/
def S3077QPrimeCoherenceTarget : Prop :=
  (∀ U, S3077MapIdTarget U) ∧
  (∀ {U V W} (f : U ⟶ V) (g : V ⟶ W), S3077MapCompTarget f g)



abbrev S3077IdMor
    (U : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ)) : U ⟶ U := 𝟙 U

noncomputable abbrev S3077IdFst
    (U : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ))
    (P : S3048SignTorsorFiber U) :
    (S3073PullbackFiber (𝟙 U) P).total ⟶ P.total :=
  pullback.fst (f := P.projection) (g := (S3077IdMor U).as.unop)

noncomputable abbrev S3077IdInv
    (U : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ))
    (P : S3048SignTorsorFiber U) :
    P.total ⟶ (S3073PullbackFiber (𝟙 U) P).total :=
  pullback.lift (𝟙 P.total) P.projection (by simp)

theorem S3077_idInv_comp_fst
    (U : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ))
    (P : S3048SignTorsorFiber U) :
    S3077IdInv U P ≫ S3077IdFst U P = 𝟙 P.total := by
  change pullback.lift (𝟙 P.total) P.projection _ ≫
    pullback.fst P.projection (𝟙 (Opposite.unop U.as)) = 𝟙 P.total
  rw [pullback.lift_fst]

theorem S3077_idFst_comp_inv
    (U : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ))
    (P : S3048SignTorsorFiber U) :
    S3077IdFst U P ≫ S3077IdInv U P =
      𝟙 (S3073PullbackFiber (𝟙 U) P).total := by
  apply pullback.hom_ext (f := P.projection) (g := (S3077IdMor U).as.unop)
  · rw [Category.assoc]
    change pullback.fst P.projection (𝟙 (Opposite.unop U.as)) ≫
      (pullback.lift (𝟙 P.total) P.projection _ ≫
        pullback.fst P.projection (𝟙 (Opposite.unop U.as))) =
      𝟙 (S3073PullbackTotal (𝟙 U) P) ≫
        pullback.fst P.projection (𝟙 (Opposite.unop U.as))
    rw [pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc]
    change pullback.fst P.projection (𝟙 (Opposite.unop U.as)) ≫
      (pullback.lift (𝟙 P.total) P.projection _ ≫
        pullback.snd P.projection (𝟙 (Opposite.unop U.as))) =
      𝟙 (S3073PullbackTotal (𝟙 U) P) ≫
        pullback.snd P.projection (𝟙 (Opposite.unop U.as))
    rw [pullback.lift_snd, pullback.condition, Category.comp_id, Category.id_comp]

noncomputable def S3077MapIdComponent
    (U : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ))
    (P : S3048SignTorsorFiber U) :
    S3049TorsorIso U (S3073PullbackFiber (𝟙 U) P) P where
  hom := S3077IdFst U P
  comm := by
    change pullback.fst P.projection (𝟙 (Opposite.unop U.as)) ≫
      P.projection = pullback.snd P.projection (𝟙 (Opposite.unop U.as))
    rw [pullback.condition, Category.comp_id]
  equivariant := by
    intro g
    change pullback.fst P.projection (𝟙 (Opposite.unop U.as)) ≫ P.action g =
      (S3073PullbackFiber (𝟙 U) P).action g ≫
        pullback.fst P.projection (𝟙 (Opposite.unop U.as))
    rw [show (S3073PullbackFiber (𝟙 U) P).action g =
      S3073PullbackAction (𝟙 U) P g from rfl]
    change pullback.fst P.projection (𝟙 (Opposite.unop U.as)) ≫ P.action g =
      pullback.lift
        (pullback.fst P.projection (𝟙 (Opposite.unop U.as)) ≫ P.action g)
        (pullback.snd P.projection (𝟙 (Opposite.unop U.as))) _ ≫
        pullback.fst P.projection (𝟙 (Opposite.unop U.as))
    rw [pullback.lift_fst]
  isIso := ⟨S3077IdInv U P,
    S3077_idFst_comp_inv U P,
    S3077_idInv_comp_fst U P⟩

#check S3077IdFst
#check S3077IdInv
#check S3077_idInv_comp_fst
#check S3077_idFst_comp_inv
#check S3077MapIdComponent

#check S3077NatIsoData
#check S3077MapIdTarget
#check S3077MapCompTarget
#check S3077QPrimeCoherenceTarget

end LeanFormal.IUT.XiFPaper.S3077QPrimeCoherence
end
