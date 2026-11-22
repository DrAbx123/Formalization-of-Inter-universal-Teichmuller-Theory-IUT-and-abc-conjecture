import tmp.sheaf.xif.paper.S2631S1726SplitCoverActual
import tmp.sheaf.xif.paper.S2512StackOpenImmersionUB
import tmp.sheaf.xif.paper.S2561S2512LiftUniqueActual
import tmp.sheaf.xif.paper.S2628CoherentConstructionActual
import tmp.sheaf.xif.paper.S1866ApexCoherenceActual
import tmp.sheaf.xif.paper.S2199RepresentableStackActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual

/-! # S2632: StrongCover for the actual S1726 split cover -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
open LeanFormal.IUT.XiFPaper.S2561S2512LiftUniqueActual
open LeanFormal.IUT.XiFPaper.S2628CoherentConstructionActual
open LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1866ApexCoherenceActual
open LeanFormal.IUT.XiFPaper.S2199RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2631S1726SplitCoverActual

namespace LeanFormal.IUT.XiFPaper.S2632S1726SplitCoverStrongActual

variable (T : Iut.SchemeOverField S1726K)
variable (q : Pseudofunctor.StrongTrans
  (Iut.schemeRepresentableEtalePseudofunctor S1726K T)
  S1726Orbicurve.stack.fiber)


noncomputable def S1726SplitStack : Iut.EtaleStackOverField S1726K where
  fiber := Iut.schemeRepresentableEtalePseudofunctor S1726K S1726SplitOver
  isStack := s2199_representable_isStack S1726K S1726SplitOver
  orbicurveSignature := none

abbrev S1726AffineStack : Iut.EtaleStackOverField S1726K :=
  S1726Orbicurve.stack

noncomputable def S1726SplitStackHom :
    S1726SplitStack.Hom S1726AffineStack :=
  S1742StrongTransOfHom S1726SplitMap

noncomputable def S1726PointHom : T ⟶ S1726AffineOver :=
  S1742HomOfStrongTrans q

noncomputable abbrev S1726SplitPullback : Iut.SchemeOverField S1726K :=
  Over.mk (pullback.fst S1726SplitMap.left (S1726PointHom T q).left ≫
    S1726SplitOver.hom)

noncomputable def S1726SplitToSource :
    S1726SplitPullback T q ⟶ S1726SplitOver :=
  Over.homMk (pullback.fst S1726SplitMap.left (S1726PointHom T q).left)
    (by rfl)

noncomputable def S1726SplitProjection :
    S1726SplitPullback T q ⟶ T :=
  Over.homMk (pullback.snd S1726SplitMap.left (S1726PointHom T q).left) (by
    show pullback.snd S1726SplitMap.left (S1726PointHom T q).left ≫ T.hom =
      pullback.fst S1726SplitMap.left (S1726PointHom T q).left ≫
        S1726SplitOver.hom
    rw [← (S1726PointHom T q).w, ← S1726SplitMap.w]
    rw [← Category.assoc, ← Category.assoc]
    rw [← pullback.condition])

theorem S1726SplitIsPullback :
    IsPullback (S1726SplitToSource T q).left (S1726SplitProjection T q).left
      S1726SplitMap.left (S1726PointHom T q).left :=
  IsPullback.of_hasPullback S1726SplitMap.left (S1726PointHom T q).left

theorem S1726SplitSquareCommutesHom :
    S1726SplitToSource T q ≫ S1726SplitMap =
      S1726SplitProjection T q ≫ S1726PointHom T q := by
  apply Over.OverMorphism.ext
  show pullback.fst S1726SplitMap.left (S1726PointHom T q).left ≫
      S1726SplitMap.left =
    pullback.snd S1726SplitMap.left (S1726PointHom T q).left ≫
      (S1726PointHom T q).left
  exact pullback.condition

theorem S1726SplitCommutesVal
    (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (a : (S2512YS (F := S1726K) (S1726SplitPullback T q)).obj U) :
    S2512Val (F := S1726K) (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S1726SplitToSource T q))
        (S1742StrongTransOfHom S1726SplitMap)) U a =
      S2512Val (F := S1726K) (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S1726SplitProjection T q))
        q) U a := by
  rw [S2512Val_vcomp, S2512Val_vcomp]
  rw [S2512Val_strongTransOfHom, S2512Val_strongTransOfHom]
  rw [S1742HomOfStrongTrans_strongTransOfHom]
  calc
    (a.as ≫ S1726SplitToSource T q) ≫ S1726SplitMap
        = a.as ≫ (S1726SplitToSource T q ≫ S1726SplitMap) := by
          rw [Category.assoc]
    _ = a.as ≫ (S1726SplitProjection T q ≫ S1726PointHom T q) := by
          rw [S1726SplitSquareCommutesHom]
    _ = (a.as ≫ S1726SplitProjection T q) ≫ S1726PointHom T q := by
          rw [Category.assoc]

noncomputable def S1726SplitSquare :
    EtalePseudofunctorSquare
      (S2512YS (F := S1726K) (S1726SplitPullback T q))
      (S2512YS (F := S1726K) S1726SplitOver)
      (S2512YS (F := S1726K) T)
      (S2512YS (F := S1726K) S1726AffineOver) where
  toX := S1742StrongTransOfHom (S1726SplitToSource T q)
  toY := S1742StrongTransOfHom (S1726SplitProjection T q)
  xToBase := S1742StrongTransOfHom S1726SplitMap
  yToBase := q
  commutes := (S2512Val_isoOfValEq
    (L := Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S1726SplitToSource T q))
      (S1742StrongTransOfHom S1726SplitMap))
    (L' := Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S1726SplitProjection T q)) q)
    (S1726SplitCommutesVal T q)).some

noncomputable def S1726SplitWitness :
    (S1726SplitSquare T q).TwoPullbackWitness := by
  let sq := S1726SplitSquare T q
  have hF : S2512BaseF sq = S1726SplitMap := by
    change S1742HomOfStrongTrans sq.xToBase = S1726SplitMap
    rw [show sq.xToBase = S1742StrongTransOfHom S1726SplitMap from rfl,
      S1742HomOfStrongTrans_strongTransOfHom]
  have hG : S2512BaseG sq = S1726PointHom T q := rfl
  have hpb : IsPullback (S1726SplitToSource T q).left
      (S1726SplitProjection T q).left (S2512BaseF sq).left (S2512BaseG sq).left := by
    rw [hF, hG]
    exact S1726SplitIsPullback T q
  exact S2512Witness (P := S1726SplitPullback T q)
    (pX := S1726SplitToSource T q) (pY := S1726SplitProjection T q)
    (sq := sq) hpb rfl rfl

noncomputable def S1726SplitPresentation :
    EtaleStackBaseChangePresentation
      (source := S1726SplitStack) (target := S1726AffineStack)
      S1726SplitStackHom T q where
  pullbackScheme := S1726SplitPullback T q
  projection := S1726SplitProjection T q
  projectionMap :=
    { transformation := S1742StrongTransOfHom (S1726SplitProjection T q)
      app_eq := fun U => rfl }
  toSource := S1742StrongTransOfHom (S1726SplitToSource T q)
  commutes := (S1726SplitSquare T q).commutes
  isPullback := S1726SplitWitness T q


noncomputable def S1726SplitStrongBc :
    StrongEtaleStackBaseChangePresentation S1726SplitStackHom T q where
  toWeak := S1726SplitPresentation T q
  coneEssSurj := by
    change S1852ConeEssSurj (S1726SplitPresentation T q)
    apply coneEssSurj_of_liftUnique
    change S2558LiftUnique
      (S1852WeakSquare (S1726SplitPresentation T q))
      (S1726SplitPresentation T q).isPullback
    exact S2561S2512LiftUnique
      (pX := S1726SplitToSource T q) (pY := S1726SplitProjection T q)
      (sq := S1726SplitSquare T q)
      (by
        let sq := S1726SplitSquare T q
        have hF : S2512BaseF sq = S1726SplitMap := by
          change S1742HomOfStrongTrans sq.xToBase = S1726SplitMap
          rw [show sq.xToBase = S1742StrongTransOfHom S1726SplitMap from rfl,
            S1742HomOfStrongTrans_strongTransOfHom]
        have hG : S2512BaseG sq = S1726PointHom T q := rfl
        rw [hF, hG]
        exact S1726SplitIsPullback T q)
      rfl rfl

noncomputable def S1726SplitStrongFiniteEtale :
    StrongEtaleStackFiniteEtaleMorphism S1726SplitStackHom where
  baseChange T q := S1726SplitStrongBc T q
  hasProperty T q := by
    haveI : IsFinite S1726SplitMap.left := S1726SplitMap_isFinite
    haveI : Etale S1726SplitMap.left := S1726SplitMap_etale
    change IsFinite (pullback.snd S1726SplitMap.left
        (S1726PointHom T q).left) ∧
      Etale (pullback.snd S1726SplitMap.left (S1726PointHom T q).left)
    exact ⟨inferInstance, inferInstance⟩

noncomputable def S1726SplitCover :
    Iut.OrbicurveFiniteEtaleCover S1726Orbicurve where
  source := S1726SplitStack
  map := S1726SplitStackHom
  finiteEtale := S1726SplitStrongFiniteEtale.toWeak


noncomputable def S1726SplitStrongCoverOf :
    S1866StrongCoverOf S1726SplitCover :=
  ⟨S1726SplitStrongFiniteEtale, rfl⟩

theorem S1726SplitCoherentExists :
    ∃ C : CoherentCover, C.cover = S1726SplitCover :=
  (S1866StrongCoverOf_iff_coherent S1726SplitCover).mp
    S1726SplitStrongCoverOf

#check S1726SplitStrongCoverOf
#check S1726SplitCoherentExists
#print axioms S1726SplitStrongCoverOf
#print axioms S1726SplitCoherentExists

#check S1726SplitStrongBc
#check S1726SplitStrongFiniteEtale
#check S1726SplitCover
#print axioms S1726SplitCover

#check S1726SplitPresentation
#print axioms S1726SplitPresentation

end LeanFormal.IUT.XiFPaper.S2632S1726SplitCoverStrongActual
end
