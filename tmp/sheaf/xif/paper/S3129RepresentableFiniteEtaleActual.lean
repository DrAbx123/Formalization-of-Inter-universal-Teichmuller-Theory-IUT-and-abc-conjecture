import tmp.sheaf.xif.paper.S3129GenericRepresentablePullbackActual
import tmp.sheaf.xif.paper.S3121StrongTransVcompActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open LeanFormal.IUT.XiFPaper.S3129GenericRepresentablePullbackActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleActual

variable {F : Type} [Field F]

/-- The etale stack over F represented by a scheme. -/
noncomputable def S3129YS (S : SchemeOverField F)
    (sig : Option OrbicurveSignature := none) : EtaleStackOverField F where
  fiber := S1742YS (F := F) S
  isStack := inferInstance
  orbicurveSignature := sig

/-- The explicit scheme-level pullback object for the base change. -/
noncomputable def S3129PB {S T : SchemeOverField F} (f : S ⟶ T)
    (x : X ⟶ T) (X : SchemeOverField F) : SchemeOverField F :=
  Over.mk (pullback.fst f.left x.left ≫ S.hom)

/-- The first projection of the explicit pullback object. -/
noncomputable def S3129PFst {S T X : SchemeOverField F} (f : S ⟶ T) (x : X ⟶ T) :
    S3129PB (F := F) f x X ⟶ S :=
  Over.homMk (pullback.fst f.left x.left) (by rfl)

/-- The second projection of the explicit pullback object. -/
noncomputable def S3129PSnd {S T X : SchemeOverField F} (f : S ⟶ T) (x : X ⟶ T) :
    S3129PB (F := F) f x X ⟶ X :=
  Over.homMk (pullback.snd f.left x.left) (by
    show pullback.snd f.left x.left ≫ X.hom =
      pullback.fst f.left x.left ≫ S.hom
    calc
      pullback.snd f.left x.left ≫ X.hom =
          pullback.snd f.left x.left ≫ x.left ≫ T.hom := by rw [x.w]
      _ = pullback.fst f.left x.left ≫ f.left ≫ T.hom := by
          rw [← Category.assoc, ← Category.assoc, ← pullback.condition]
      _ = pullback.fst f.left x.left ≫ S.hom := by rw [f.w])

/-- The explicit 2-commuting square of the base change of a representable map. -/
noncomputable def S3129Square {S T : SchemeOverField F} (f : S ⟶ T)
    (X : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := F) X) (S1742YS (F := F) T)) :
    EtalePseudofunctorSquare
      (S1742YS (F := F) (S3129PB (F := F) f (S1742HomOfStrongTrans (F := F) point) X))
      (S1742YS (F := F) S) (S1742YS (F := F) X) (S1742YS (F := F) T) where
  toX := S1742StrongTransOfHom (F := F)
    (S3129PFst (F := F) f (S1742HomOfStrongTrans (F := F) point))
  toY := S1742StrongTransOfHom (F := F)
    (S3129PSnd (F := F) f (S1742HomOfStrongTrans (F := F) point))
  xToBase := S1742StrongTransOfHom (F := F) f
  yToBase := point
  commutes := by
    let x : X ⟶ T := S1742HomOfStrongTrans (F := F) point
    let P : SchemeOverField F := S3129PB (F := F) f x X
    let pX : P ⟶ S := S3129PFst (F := F) f x
    let pY : P ⟶ X := S3129PSnd (F := F) f x
    have hOver : pX ≫ f = pY ≫ x := by
      apply Comma.hom_ext
      · change pullback.fst f.left x.left ≫ f.left =
          pullback.snd f.left x.left ≫ x.left
        exact pullback.condition
      · exact Subsingleton.elim _ _
    let e1 : Iso (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := F) pX)
        (S1742StrongTransOfHom (F := F) f))
        (S1742StrongTransOfHom (F := F) (pX ≫ f)) :=
      eqToIso (S3121StrongTransOfHom_vcomp (F := F) pX f)
    let e2 : Iso (S1742StrongTransOfHom (F := F) (pX ≫ f))
        (S1742StrongTransOfHom (F := F) (pY ≫ x)) :=
      eqToIso (congrArg (S1742StrongTransOfHom (F := F)) hOver)
    let e3 : Iso (S1742StrongTransOfHom (F := F) (pY ≫ x))
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := F) pY)
          (S1742StrongTransOfHom (F := F) x)) :=
      eqToIso (S3121StrongTransOfHom_vcomp (F := F) pY x).symm
    let e4 : Iso (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := F) pY)
        (S1742StrongTransOfHom (F := F) x))
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := F) pY) point) :=
      Bicategory.whiskerLeftIso
        (a := S1742YS (F := F) P) (b := S1742YS (F := F) X) (c := S1742YS (F := F) T)
        (S1742StrongTransOfHom (F := F) pY)
        (S1742StrongTransIsoOfHom (F := F) point)
    exact e1.trans (e2.trans (e3.trans e4))

/-- The square is a two-pullback witness. -/
noncomputable def S3129Witness {S T : SchemeOverField F} (f : S ⟶ T)
    (X : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := F) X) (S1742YS (F := F) T)) :
    (S3129Square (F := F) f X point).TwoPullbackWitness :=
  S1911Witness (F := F)
    (pX := S3129PFst (F := F) f (S1742HomOfStrongTrans (F := F) point))
    (pY := S3129PSnd (F := F) f (S1742HomOfStrongTrans (F := F) point))
    (sq := S3129Square (F := F) f X point)
    (IsPullback.of_hasPullback f.left (S1742HomOfStrongTrans (F := F) point).left)
    rfl rfl


/-- Explicit base-change presentation for a representable finite-etale map. -/
noncomputable def S3129BaseChange {S T : SchemeOverField F} (f : S ⟶ T)
    (X : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := F) X) (S1742YS (F := F) T)) :
    EtaleStackBaseChangePresentation
      (source := S3129YS (F := F) S) (target := S3129YS (F := F) T)
      (S1742StrongTransOfHom (F := F) f) X point where
  pullbackScheme := S3129PB (F := F) f (S1742HomOfStrongTrans (F := F) point) X
  projection := S3129PSnd (F := F) f
    (S1742HomOfStrongTrans (F := F) point)
  projectionMap :=
    { transformation := S1742StrongTransOfHom (F := F)
        (S3129PSnd (F := F) f (S1742HomOfStrongTrans (F := F) point))
      app_eq := fun U => rfl }
  toSource := S1742StrongTransOfHom (F := F)
    (S3129PFst (F := F) f (S1742HomOfStrongTrans (F := F) point))
  commutes := (S3129Square (F := F) f X point).commutes
  isPullback := S3129Witness (F := F) f X point

/-- A representable map with scheme-level finite-etale property is representably
finite etale. -/
noncomputable def S3129RepresentableFiniteEtale {S T : SchemeOverField F}
    (f : S ⟶ T) [AlgebraicGeometry.IsFinite f.left]
    [AlgebraicGeometry.Etale f.left] :
    EtaleStackFiniteEtaleMorphism
      (source := S3129YS (F := F) S) (target := S3129YS (F := F) T)
      (S1742StrongTransOfHom (F := F) f) where
  baseChange := S3129BaseChange (F := F) f
  hasProperty X point := by
    let x : X ⟶ T := S1742HomOfStrongTrans (F := F) point
    dsimp only [S3129BaseChange, S3129PSnd]
    change AlgebraicGeometry.IsFinite (pullback.snd f.left x.left) ∧
      AlgebraicGeometry.Etale (pullback.snd f.left x.left)
    exact ⟨inferInstance, inferInstance⟩



/-- Signature-parametrized form of the representable finite-etale theorem. -/
noncomputable def S3129RepresentableFiniteEtaleWithSig {S T : SchemeOverField F}
    (sigS sigT : Option OrbicurveSignature) (f : S ⟶ T)
    [AlgebraicGeometry.IsFinite f.left]
    [AlgebraicGeometry.Etale f.left] :
    EtaleStackFiniteEtaleMorphism
      (source := S3129YS (F := F) S sigS)
      (target := S3129YS (F := F) T sigT)
      (S1742StrongTransOfHom (F := F) f) where
  baseChange T q :=
    { pullbackScheme := (S3129BaseChange (F := F) f T q).pullbackScheme
      projection := (S3129BaseChange (F := F) f T q).projection
      projectionMap := (S3129BaseChange (F := F) f T q).projectionMap
      toSource := (S3129BaseChange (F := F) f T q).toSource
      commutes := (S3129BaseChange (F := F) f T q).commutes
      isPullback := (S3129BaseChange (F := F) f T q).isPullback }
  hasProperty T q := (S3129RepresentableFiniteEtale (F := F) f).hasProperty T q


#check S3129RepresentableFiniteEtaleWithSig
#check S3129BaseChange
#check S3129RepresentableFiniteEtale
#check S3129YS
#check S3129Square
#check S3129Witness

end LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleActual
end