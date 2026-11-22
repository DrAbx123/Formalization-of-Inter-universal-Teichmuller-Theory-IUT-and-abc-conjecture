import tmp.sheaf.xif.paper.RepresentableCoverChosenCategoryActual
import tmp.sheaf.xif.paper._TransportE2E3Agent
import tmp.sheaf.xif.paper.S3129RepresentableFiniteEtaleActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3119StrongTransEqActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S2812IsStackActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S2541FiniteEtaleTransportIsoActual
open LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual

variable {l : PrimeGeFive}

/-- Forget the chosen scheme: a S3127 cover is an ordinary finite-etale cover. -/
noncomputable def S3127ToOrbicurveCover (A : S3127Cover (l := l)) :
    OrbicurveFiniteEtaleCover (S1536XF (l := l)) where
  source := S3127Source (l := l) A.scheme
  map := A.map
  finiteEtale := by
    let f : A.scheme ⟶ S1419AffineOver (l := l) :=
      S1742HomOfStrongTrans (F := S1348K l) A.map
    let sig := (S1536XF (l := l)).stack.orbicurveSignature
    let hf : EtaleStackFiniteEtaleMorphism
        (source := S3127Source (l := l) A.scheme)
        (target := (S1536XF (l := l)).stack)
        (S1742StrongTransOfHom (F := S1348K l) f) :=
      by
        haveI hfin : AlgebraicGeometry.IsFinite f.left := A.finiteEtale.1
        haveI het : AlgebraicGeometry.Etale f.left := A.finiteEtale.2
        exact S3129RepresentableFiniteEtaleWithSig (F := S1348K l) sig sig f
    let e : Iso (S1742StrongTransOfHom (F := S1348K l) f) A.map :=
      S1742StrongTransIsoOfHom (F := S1348K l) A.map
    exact S2541FiniteEtaleTransportIso e hf

/-- Forward map: a raw S3127 map gives an ordinary cover map. -/
noncomputable def S3127ToCoverMap {A B : S3127Cover (l := l)}
    (f : S3127RepMap A B) :
    OrbicurveFiniteEtaleCoverMap
      (S3127ToOrbicurveCover A) (S3127ToOrbicurveCover B) where
  map := S1742StrongTransOfHom (F := S1348K l) f.hom
  commutes := f.commutes.some

/-- Backward map: an ordinary cover map between representable covers gives a
raw S3127 map. -/
noncomputable def S3127CoverMapOfRaw {A B : S3127Cover (l := l)}
    (F : OrbicurveFiniteEtaleCoverMap
      (S3127ToOrbicurveCover A) (S3127ToOrbicurveCover B)) :
    S3127RepMap A B where
  hom := S1742HomOfStrongTrans (F := S1348K l) F.map
  commutes := by
    let amap : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) A.scheme)
        (S1536XF (l := l)).stack.fiber := A.map
    let bmap : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) B.scheme)
        (S1536XF (l := l)).stack.fiber := B.map
    let Fmap : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) A.scheme)
        (S1742YS (F := S1348K l) B.scheme) := F.map
    let e : Iso (S1742StrongTransOfHom (F := S1348K l)
          (S1742HomOfStrongTrans (F := S1348K l) Fmap)) Fmap :=
      S1742StrongTransIsoOfHom (F := S1348K l) Fmap
    have hcomm : Iso (Pseudofunctor.StrongTrans.vcomp Fmap bmap) amap := F.commutes
    exact ⟨(Bicategory.whiskerRightIso
      (a := S1742YS (F := S1348K l) A.scheme)
      (b := S1742YS (F := S1348K l) B.scheme)
      (c := (S1536XF (l := l)).stack.fiber) e bmap).trans hcomm⟩

/-- The forward map is injective. -/
theorem S3127ToCoverMap_injective {A B : S3127Cover (l := l)}
    {f g : S3127RepMap A B}
    (h : S3127ToCoverMap (l := l) f = S3127ToCoverMap (l := l) g) :
    f = g := by
  let F : OrbicurveFiniteEtaleCoverMap
      (S3127ToOrbicurveCover A) (S3127ToOrbicurveCover B) := S3127ToCoverMap f
  let G : OrbicurveFiniteEtaleCoverMap
      (S3127ToOrbicurveCover A) (S3127ToOrbicurveCover B) := S3127ToCoverMap g
  have hmap : F.map = G.map := congrArg
    (fun H : OrbicurveFiniteEtaleCoverMap
      (S3127ToOrbicurveCover A) (S3127ToOrbicurveCover B) => H.map) h
  let etaF : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) A.scheme)
      (S1742YS (F := S1348K l) B.scheme) := F.map
  let etaG : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) A.scheme)
      (S1742YS (F := S1348K l) B.scheme) := G.map
  have hmap' : etaF = etaG := hmap
  have hmap'' : S1742StrongTransOfHom (F := S1348K l) f.hom =
      S1742StrongTransOfHom (F := S1348K l) g.hom := by
    simpa [S3127ToCoverMap, F, G, etaF, etaG] using hmap'
  have hhom : f.hom = g.hom := by
    have := congrArg (S1742HomOfStrongTrans (F := S1348K l)
      (S := A.scheme) (T := B.scheme)) hmap''
    simpa [S1742HomOfStrongTrans_strongTransOfHom] using this
  exact S3127RepMap_ext f g hhom




/-- All 2-cells between strong transformations of representable fibers are
subsingleton. -/
theorem S3127HomSubsingleton
    {S T : SchemeOverField (S1348K l)}
    {eta theta : Pseudofunctor.StrongTrans
      (S1742YS (F := S1348K l) S) (S1742YS (F := S1348K l) T)}
    (h1 h2 : eta ⟶ theta) : h1 = h2 := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- Isomorphisms between fixed representable strong transformations are equal. -/
theorem S3127IsoSubsingleton
    {S T : SchemeOverField (S1348K l)}
    {eta theta : Pseudofunctor.StrongTrans
      (S1742YS (F := S1348K l) S) (S1742YS (F := S1348K l) T)}
    (e1 e2 : eta ≅ theta) : e1 = e2 := by
  apply CategoryTheory.Iso.ext
  exact S3127HomSubsingleton e1.hom e2.hom






/-- Sigma presentation of an ordinary cover map: its underlying strong
transformation together with the commuting 2-isomorphism. -/
abbrev S3127CoverMapSigma (A B : S3127Cover (l := l)) : Type 1 :=
  Sigma (fun m : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) A.scheme)
      (S1742YS (F := S1348K l) B.scheme) =>
    Iso (Pseudofunctor.StrongTrans.vcomp m B.map) A.map)

/-- Forget the Sigma presentation. -/
noncomputable def S3127OfSigma {A B : S3127Cover (l := l)}
    (s : S3127CoverMapSigma A B) :
    OrbicurveFiniteEtaleCoverMap
      (S3127ToOrbicurveCover A) (S3127ToOrbicurveCover B) :=
  OrbicurveFiniteEtaleCoverMap.mk (X := S1536XF (l := l))
    (source := S3127ToOrbicurveCover A)
    (target := S3127ToOrbicurveCover B) s.1 s.2

/-- Package an ordinary cover map as a Sigma. -/
noncomputable def S3127ToSigma {A B : S3127Cover (l := l)}
    (F : OrbicurveFiniteEtaleCoverMap
      (S3127ToOrbicurveCover A) (S3127ToOrbicurveCover B)) :
    S3127CoverMapSigma A B :=
  ⟨F.map, F.commutes⟩

theorem S3127OfSigma_toSigma {A B : S3127Cover (l := l)}
    (F : OrbicurveFiniteEtaleCoverMap
      (S3127ToOrbicurveCover A) (S3127ToOrbicurveCover B)) :
    S3127OfSigma (S3127ToSigma F) = F := by
  cases F with
  | mk Fmap Fcomm => rfl


/-- The backward map is a section of the forward map. -/
theorem S3127CoverMapOfRaw_toCoverMap {A B : S3127Cover (l := l)}
    (f : S3127RepMap A B) :
    S3127CoverMapOfRaw (S3127ToCoverMap f) = f := by
  apply S3127RepMap_ext
  dsimp only [S3127CoverMapOfRaw, S3127ToCoverMap]
  rw [S1742HomOfStrongTrans_strongTransOfHom]


/-- The forward map is surjective onto ordinary cover maps. -/
theorem S3127ToCoverMap_ofRaw {A B : S3127Cover (l := l)}
    (F : OrbicurveFiniteEtaleCoverMap
      (S3127ToOrbicurveCover A) (S3127ToOrbicurveCover B)) :
    S3127ToCoverMap (S3127CoverMapOfRaw F) = F := by
  let G := S3127CoverMapOfRaw (l := l) F
  have hmap : (S3127ToCoverMap (l := l) G).map = F.map := by
    apply S3119StrongTrans_eq_of_hom_eq
    simp [G, S3127ToCoverMap, S3127CoverMapOfRaw,
      S1742HomOfStrongTrans_strongTransOfHom]
  have hsig : S3127ToSigma (S3127ToCoverMap (l := l) G) =
      S3127ToSigma F := by
    apply Sigma.ext hmap
    let c1 : Iso (Pseudofunctor.StrongTrans.vcomp
        (S3127ToCoverMap (l := l) G).map B.map) A.map :=
      (S3127ToSigma (S3127ToCoverMap (l := l) G)).2
    let c1' : Iso (Pseudofunctor.StrongTrans.vcomp F.map B.map) A.map :=
      hmap ▸ c1
    have hc : c1' = F.commutes := S3127IsoSubsingleton c1' F.commutes
    have hHEq : HEq c1 F.commutes := by
      have h := eqRec_heq
        (φ := fun m : Pseudofunctor.StrongTrans
          (S1742YS (F := S1348K l) A.scheme)
          (S1742YS (F := S1348K l) B.scheme) =>
          Iso (Pseudofunctor.StrongTrans.vcomp m B.map) A.map) hmap c1
      exact h.symm.trans (heq_of_eq hc)
    exact hHEq
  calc
    S3127ToCoverMap (l := l) G =
        S3127OfSigma (S3127ToSigma (S3127ToCoverMap (l := l) G)) :=
      (S3127OfSigma_toSigma (S3127ToCoverMap (l := l) G)).symm
    _ = S3127OfSigma (S3127ToSigma F) := by rw [hsig]
    _ = F := S3127OfSigma_toSigma F

/-- The forward map is surjective. -/
theorem S3127ToCoverMap_surjective (A B : S3127Cover (l := l)) :
    Function.Surjective
      (fun f : A ⟶ B => S3127ToCoverMap (l := l) f) :=
  fun F => ⟨S3127CoverMapOfRaw (l := l) F,
    S3127ToCoverMap_ofRaw (l := l) F⟩

/-- The forward map is bijective. -/
theorem S3127ToCoverMap_bijective (A B : S3127Cover (l := l)) :
    Function.Bijective
      (fun f : A ⟶ B => S3127ToCoverMap (l := l) f) :=
  ⟨fun f g h => S3127ToCoverMap_injective (l := l) h,
    S3127ToCoverMap_surjective (l := l) A B⟩


/-- Essential-surjectivity gap: every ordinary finite-etale cover has a
representable source. -/
def S3127EssentialSurjectiveTarget : Prop :=
  forall C : OrbicurveFiniteEtaleCover (S1536XF (l := l)),
    exists A : S3127Cover (l := l),
      S3127ToOrbicurveCover A = C

/-- Target: the forward map from S3127 maps to ordinary cover maps is bijective. -/
def S3127CoverMorphismBijectiveTarget : Prop :=
  forall (A B : S3127Cover (l := l)),
    Function.Bijective (fun f : A ⟶ B => S3127ToCoverMap (l := l) f)

/-- The named bijectivity target is inhabited. -/
theorem S3127CoverMorphismBijectiveTarget_proof :
    S3127CoverMorphismBijectiveTarget (l := l) :=
  fun A B => S3127ToCoverMap_bijective (l := l) A B


#check S3127ToOrbicurveCover
#check S3127ToCoverMap
#check S3127CoverMapOfRaw_toCoverMap
#check S3127ToCoverMap_ofRaw
#check S3127ToCoverMap_surjective
#check S3127ToCoverMap_bijective
#check S3127CoverMorphismBijectiveTarget_proof
#check S3127EssentialSurjectiveTarget

end LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
end