import tmp.sheaf.xif.paper.S2086ToAAssemblyActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# S2130: the explicit scheme-level base change of a cover map

## What the review suggested, and what is done here

For a cover map `T -> C` (in the application `T = ptA ; f.map`) the suggested
construction of `B x_C T` is the strict fibre product

  `B x_C T = (B x_X T) x_{C x_X T} T`,

where the second factor is the graph/section of `T -> C x_X T`.  The graph is
the section of the finite-etale projection `C x_X T -> T`; it is both an open
and a closed immersion.  Hence the projection of the strict fibre product to
`T` is finite etale, and the construction gives the cover-map certificate
`hg` (representable finite etaleness of `g.map`) together with the canonical
presentation 2-cell.

This file implements the scheme-level part:

* `S2130PC` is the actual finite-etale presentation of `C.map` at the
  C-point `ptA ; f.map`, obtained from `C.finiteEtale`.
* `S2130Graph` is the graph of that point, i.e. the 2-Yoneda scheme morphism
  `T -> C x_X T`; `S2130Graph_projection` proves it is a section of the
  finite-etale projection.
* `S2130Graph_open` and `S2130Graph_closed` prove that the graph is an open
  and a closed immersion.  The open proof uses `Etale.of_comp` (the graph is a
  section of an etale map) and `IsOpenImmersion.of_flat_of_mono`; the closed
  proof uses `IsFinite.of_comp` and `IsClosedImmersion.iff_isFinite_and_mono`.
* `S2130Phi` is the comparison `B x_X T -> C x_X T` over `T`, constructed
  from the two-pullback witness of the C-presentation; `S2130Phi_projection`
  records its projection to `T`.
* `S2130P`, `S2130P_fst`, `S2130P_snd` are the strict fibre product
  `(B x_X T) x_{C x_X T} T`; `S2130P_snd_finite` and `S2130P_snd_etale`
  prove unconditionally that its projection is finite etale.
* `S2130ToSource`, `S2130Proj`, `S2130Commutes` assemble the concrete
  base-change square of `g.map` at `ptA ; f.map`, over the scheme
  `S2130P`.

## The exact first missing

The strict fibre product `S2130P` is a 1-categorical fibre product of
schemes.  To turn it into an `EtaleStackBaseChangePresentation` one still has
to identify it with the *bicategorical* pullback of `g.map` along the
C-point.  That is exactly

  `S2130ConcreteTwoPullback`:
  for every `A B C f g T ptA`, the concrete square
  `(S2130ToSource, S2130Proj, g.map, ptA ; f.map)` is a
  `TwoPullbackWitness`.

This is 2-categorical bookkeeping (Yoneda preservation of the strict fibre
product), not scheme-level geometry: the scheme-level object, its finite-etale
projection, and the comparison 2-cell are constructed.  No presentation field
is added to any existing structure and no witness is fabricated.

From the missing witness this file constructs the actual
`EtaleStackBaseChangePresentation` and the restricted `hg` at exactly the
C-points used by S2086 (`S2130ConcreteHgOfTwoPullback`), and reduces the
S2086/D6(c) assembly to the same concrete presentation plus the butterfly
witness `S2130ConcreteButterfly` (`S2130D6FiniteEtaleOfConcreteTwoPullback`).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual
open LeanFormal.IUT.XiFPaper.S2069D6CompositionClosureActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual

universe u

noncomputable def S2130PtC {A C : S1728Cover} (f : S1728CoverMap A C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber :=
  S2086PointC f ptA

noncomputable def S2130PtX {A C : S1728Cover} (f : S1728CoverMap A C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) S1726Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.vcomp (S2130PtC f T ptA) C.map

noncomputable def S2130PC {A C : S1728Cover} (f : S1728CoverMap A C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    EtaleStackBaseChangePresentation C.map T (S2130PtX f T ptA) :=
  C.finiteEtale.baseChange T (S2130PtX f T ptA)

noncomputable def S2130GraphCone {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    (EtalePseudofunctorSquare.mk (S2130PC f T ptA).toSource
      (S2130PC f T ptA).projectionMap.transformation C.map
      (S2130PtX f T ptA) (S2130PC f T ptA).commutes).Cone
      (schemeRepresentableEtalePseudofunctor S1726K T) where
  toX := S2130PtC f T ptA
  toY := Pseudofunctor.StrongTrans.id (schemeRepresentableEtalePseudofunctor S1726K T)
  commutes := (Pseudofunctor.StrongTrans.leftUnitor (S2130PtX f T ptA)).symm

noncomputable def S2130GraphSite {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T)
      (schemeRepresentableEtalePseudofunctor S1726K (S2130PC f T ptA).pullbackScheme) :=
  (S2130PC f T ptA).isPullback.lift
    (schemeRepresentableEtalePseudofunctor S1726K T)
    (S2130GraphCone f g T ptA)

noncomputable def S2130Graph {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    T ⟶ (S2130PC f T ptA).pullbackScheme :=
  S1742HomOfStrongTrans (S2130GraphSite f g T ptA)


noncomputable def S2130PB {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    EtaleStackBaseChangePresentation B.map T (S2130PtX f T ptA) :=
  B.finiteEtale.baseChange T (S2130PtX f T ptA)

noncomputable def S2130PhiCone {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    (EtalePseudofunctorSquare.mk (S2130PC f T ptA).toSource
      (S2130PC f T ptA).projectionMap.transformation C.map
      (S2130PtX f T ptA) (S2130PC f T ptA).commutes).Cone
      (schemeRepresentableEtalePseudofunctor S1726K (S2130PB f g T ptA).pullbackScheme) where
  toX := Pseudofunctor.StrongTrans.vcomp (S2130PB f g T ptA).toSource g.map
  toY := (S2130PB f g T ptA).projectionMap.transformation
  commutes :=
    (S2058AssociatorIso (S2130PB f g T ptA).toSource g.map C.map).trans
      ((S2058WhiskerLeftIso (S2130PB f g T ptA).toSource
        (Pseudofunctor.StrongTrans.vcomp g.map C.map) B.map g.commutes).trans
        (S2130PB f g T ptA).commutes)

noncomputable def S2130PhiSite {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K (S2130PB f g T ptA).pullbackScheme)
      (schemeRepresentableEtalePseudofunctor S1726K (S2130PC f T ptA).pullbackScheme) :=
  (S2130PC f T ptA).isPullback.lift
    (schemeRepresentableEtalePseudofunctor S1726K (S2130PB f g T ptA).pullbackScheme)
    (S2130PhiCone f g T ptA)

noncomputable def S2130Phi {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    (S2130PB f g T ptA).pullbackScheme ⟶ (S2130PC f T ptA).pullbackScheme :=
  S1742HomOfStrongTrans (S2130PhiSite f g T ptA)

theorem S2130HomOfStrongTrans_id {S : SchemeOverField S1726K} :
    S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.id (schemeRepresentableEtalePseudofunctor S1726K S)) =
      𝟙 S := by
  rfl

theorem S2130HomOfStrongTrans_vcomp {S U V : SchemeOverField S1726K}
    (eta : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K S)
      (schemeRepresentableEtalePseudofunctor S1726K U))
    (theta : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K U)
      (schemeRepresentableEtalePseudofunctor S1726K V)) :
    S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.vcomp eta theta) =
      S1742HomOfStrongTrans eta ≫ S1742HomOfStrongTrans theta := by
  change (((theta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
    ((eta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
      (Discrete.mk (𝟙 S)))).as) =
    S1742HomOfStrongTrans eta ≫ S1742HomOfStrongTrans theta
  have hobj : (theta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
      ((eta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
        (Discrete.mk (𝟙 S))) =
      (theta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
        (Discrete.mk (S1742HomOfStrongTrans eta)) :=
    congrArg (fun x => (theta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj x)
      (Discrete.mk_as ((eta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
        (Discrete.mk (𝟙 S)))).symm
  rw [hobj]
  rw [S1742Key theta (LocallyDiscrete.mk (Opposite.op S)) (S1742HomOfStrongTrans eta)]

theorem S2130HomOfStrongTrans_schemeRepresentableMap {S U : SchemeOverField S1726K}
    (φ : S ⟶ U) (M : SchemeRepresentableMap φ) :
    S1742HomOfStrongTrans M.transformation = φ := by
  change (((M.transformation.app
    (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
      (Discrete.mk (𝟙 S))).as) = φ
  rw [M.app_eq]
  rfl

theorem S2130Graph_projection {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    S2130Graph f g T ptA ≫ (S2130PC f T ptA).projection = 𝟙 T := by
  have e := (S2130PC f T ptA).isPullback.liftToY
    (schemeRepresentableEtalePseudofunctor S1726K T) (S2130GraphCone f g T ptA)
  have h := S1742HomOfStrongTrans_congr e
  rw [S2130HomOfStrongTrans_vcomp,
    S2130HomOfStrongTrans_schemeRepresentableMap (S2130PC f T ptA).projection
      (S2130PC f T ptA).projectionMap] at h
  have hid : S1742HomOfStrongTrans (S2130GraphCone f g T ptA).toY = 𝟙 T := rfl
  rw [hid] at h
  exact h

theorem S2130Graph_projection_left {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    (S2130Graph f g T ptA).left ≫ (S2130PC f T ptA).projection.left = 𝟙 T.left := by
  have h := congrArg Over.Hom.left (S2130Graph_projection f g T ptA)
  simpa using h

theorem S2130Graph_open {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    IsOpenImmersion (S2130Graph f g T ptA).left := by
  have hsec := S2130Graph_projection_left f g T ptA
  haveI hq_fin : IsFinite (S2130PC f T ptA).projection.left :=
    (C.finiteEtale.hasProperty T (S2130PtX f T ptA)).1
  haveI hq_et : Etale (S2130PC f T ptA).projection.left :=
    (C.finiteEtale.hasProperty T (S2130PtX f T ptA)).2
  haveI hcomp : Etale ((S2130Graph f g T ptA).left ≫ (S2130PC f T ptA).projection.left) := by
    rw [hsec]
    infer_instance
  haveI hLFTq : LocallyOfFiniteType (S2130PC f T ptA).projection.left := inferInstance
  haveI hFUq : FormallyUnramified (S2130PC f T ptA).projection.left := inferInstance
  haveI hEt : Etale (S2130Graph f g T ptA).left :=
    Etale.of_comp (f := (S2130Graph f g T ptA).left) (S2130PC f T ptA).projection.left
  haveI hFlat : Flat (S2130Graph f g T ptA).left := inferInstance
  haveI hLFP : LocallyOfFinitePresentation (S2130Graph f g T ptA).left := inferInstance
  haveI hSplit : IsSplitMono (S2130Graph f g T ptA).left :=
    IsSplitMono.mk' { retraction := (S2130PC f T ptA).projection.left, id := hsec }
  exact IsOpenImmersion.of_flat_of_mono (S2130Graph f g T ptA).left

theorem S2130Graph_closed {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    IsClosedImmersion (S2130Graph f g T ptA).left := by
  have hsec := S2130Graph_projection_left f g T ptA
  haveI hq_fin : IsFinite (S2130PC f T ptA).projection.left :=
    (C.finiteEtale.hasProperty T (S2130PtX f T ptA)).1
  haveI hcomp : IsFinite ((S2130Graph f g T ptA).left ≫ (S2130PC f T ptA).projection.left) := by
    rw [hsec]
    infer_instance
  haveI hSep : IsSeparated (S2130PC f T ptA).projection.left := inferInstance
  haveI hfin : IsFinite (S2130Graph f g T ptA).left :=
    IsFinite.of_comp (S2130Graph f g T ptA).left (S2130PC f T ptA).projection.left
  haveI hSplit : IsSplitMono (S2130Graph f g T ptA).left :=
    IsSplitMono.mk' { retraction := (S2130PC f T ptA).projection.left, id := hsec }
  exact (IsClosedImmersion.iff_isFinite_and_mono (S2130Graph f g T ptA).left).mpr
    ⟨hfin, inferInstance⟩


theorem S2130Phi_projection {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    S2130Phi f g T ptA ≫ (S2130PC f T ptA).projection =
      (S2130PB f g T ptA).projection := by
  have e := (S2130PC f T ptA).isPullback.liftToY
    (schemeRepresentableEtalePseudofunctor S1726K (S2130PB f g T ptA).pullbackScheme)
    (S2130PhiCone f g T ptA)
  have h := S1742HomOfStrongTrans_congr e
  rw [S2130HomOfStrongTrans_vcomp,
    S2130HomOfStrongTrans_schemeRepresentableMap (S2130PC f T ptA).projection
      (S2130PC f T ptA).projectionMap] at h
  have htoY : S1742HomOfStrongTrans (S2130PhiCone f g T ptA).toY =
      (S2130PB f g T ptA).projection :=
    S2130HomOfStrongTrans_schemeRepresentableMap (S2130PB f g T ptA).projection
      (S2130PB f g T ptA).projectionMap
  rw [htoY] at h
  exact h


noncomputable def S2130P {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    SchemeOverField S1726K :=
  Over.mk (Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left ≫
    (S2130PB f g T ptA).pullbackScheme.hom)

noncomputable def S2130P_fst {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    S2130P f g T ptA ⟶ (S2130PB f g T ptA).pullbackScheme :=
  Over.homMk (Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left) rfl

noncomputable def S2130P_snd {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    S2130P f g T ptA ⟶ T :=
  Over.homMk (Limits.pullback.snd (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left) (by
    have hcond := Limits.pullback.condition (f := (S2130Phi f g T ptA).left)
      (g := (S2130Graph f g T ptA).left)
    have h1 := congrArg (fun k => k ≫ (S2130PC f T ptA).pullbackScheme.hom) hcond
    rw [Category.assoc, Category.assoc, Over.w (S2130Phi f g T ptA),
      Over.w (S2130Graph f g T ptA)] at h1
    exact h1.symm)

theorem S2130P_snd_eq {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    S2130P_snd f g T ptA = S2130P_fst f g T ptA ≫ (S2130PB f g T ptA).projection := by
  apply Over.OverMorphism.ext
  show Limits.pullback.snd (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left =
    Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left ≫
      (S2130PB f g T ptA).projection.left
  calc
    Limits.pullback.snd (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left =
        Limits.pullback.snd (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left ≫
          𝟙 T.left := (Category.comp_id _).symm
    _ = Limits.pullback.snd (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left ≫
          ((S2130Graph f g T ptA).left ≫ (S2130PC f T ptA).projection.left) := by
        rw [S2130Graph_projection_left]
    _ = (Limits.pullback.snd (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left ≫
          (S2130Graph f g T ptA).left) ≫ (S2130PC f T ptA).projection.left := by
        rw [Category.assoc]
    _ = (Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left ≫
          (S2130Phi f g T ptA).left) ≫ (S2130PC f T ptA).projection.left := by
        rw [Limits.pullback.condition]
    _ = Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left ≫
          ((S2130Phi f g T ptA).left ≫ (S2130PC f T ptA).projection.left) := by
        rw [Category.assoc]
    _ = Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left ≫
          (S2130PB f g T ptA).projection.left := by
        rw [show (S2130Phi f g T ptA).left ≫ (S2130PC f T ptA).projection.left =
          (S2130PB f g T ptA).projection.left from by
            simpa using congrArg Over.Hom.left (S2130Phi_projection f g T ptA)]

theorem S2130P_snd_finite {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    IsFinite (S2130P_snd f g T ptA).left := by
  haveI hg_closed : IsClosedImmersion (S2130Graph f g T ptA).left :=
    S2130Graph_closed f g T ptA
  haveI hfst_closed : IsClosedImmersion (S2130P_fst f g T ptA).left := by
    change IsClosedImmersion
      (Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left)
    exact inferInstance
  haveI hfst_fin : IsFinite (S2130P_fst f g T ptA).left := by
    change IsFinite
      (Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left)
    exact inferInstance
  haveI hPB_fin : IsFinite (S2130PB f g T ptA).projection.left :=
    (B.finiteEtale.hasProperty T (S2130PtX f T ptA)).1
  have h : (S2130P_snd f g T ptA).left =
      (S2130P_fst f g T ptA).left ≫ (S2130PB f g T ptA).projection.left :=
    congrArg Over.Hom.left (S2130P_snd_eq f g T ptA)
  rw [h]
  exact inferInstance

theorem S2130P_snd_etale {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Etale (S2130P_snd f g T ptA).left := by
  haveI hg_open : IsOpenImmersion (S2130Graph f g T ptA).left :=
    S2130Graph_open f g T ptA
  haveI hfst_open : IsOpenImmersion (S2130P_fst f g T ptA).left := by
    change IsOpenImmersion
      (Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left)
    exact inferInstance
  haveI hfst_et : Etale (S2130P_fst f g T ptA).left := by
    change Etale
      (Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left)
    exact inferInstance
  haveI hPB_et : Etale (S2130PB f g T ptA).projection.left :=
    (B.finiteEtale.hasProperty T (S2130PtX f T ptA)).2
  have h : (S2130P_snd f g T ptA).left =
      (S2130P_fst f g T ptA).left ≫ (S2130PB f g T ptA).projection.left :=
    congrArg Over.Hom.left (S2130P_snd_eq f g T ptA)
  rw [h]
  exact inferInstance


noncomputable def S2130P_fst_site {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K (S2130P f g T ptA))
      (schemeRepresentableEtalePseudofunctor S1726K (S2130PB f g T ptA).pullbackScheme) :=
  S1742StrongTransOfHom (S2130P_fst f g T ptA)

noncomputable def S2130P_snd_site {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K (S2130P f g T ptA))
      (schemeRepresentableEtalePseudofunctor S1726K T) :=
  S1742StrongTransOfHom (S2130P_snd f g T ptA)

noncomputable def S2130ToSource {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K (S2130P f g T ptA))
      B.source.fiber :=
  Pseudofunctor.StrongTrans.vcomp (S2130P_fst_site f g T ptA)
    (S2130PB f g T ptA).toSource

noncomputable def S2130Proj {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K (S2130P f g T ptA))
      (schemeRepresentableEtalePseudofunctor S1726K T) :=
  S2130P_snd_site f g T ptA

noncomputable def S2130IsoOfHomEq {S U : SchemeOverField S1726K}
    (eta theta : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K S)
      (schemeRepresentableEtalePseudofunctor S1726K U))
    (h : S1742HomOfStrongTrans eta = S1742HomOfStrongTrans theta) : Iso eta theta :=
  (S1742StrongTransIsoOfHom eta).symm.trans
    ((eqToIso (congrArg S1742StrongTransOfHom h)).trans (S1742StrongTransIsoOfHom theta))

theorem S2130CompositeHomEq {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    S1742HomOfStrongTrans
        (Pseudofunctor.StrongTrans.vcomp (S2130P_fst_site f g T ptA)
          (S2130PhiSite f g T ptA)) =
      S1742HomOfStrongTrans
        (Pseudofunctor.StrongTrans.vcomp (S2130P_snd_site f g T ptA)
          (S2130GraphSite f g T ptA)) := by
  rw [S2130HomOfStrongTrans_vcomp, S2130HomOfStrongTrans_vcomp]
  rw [show S1742HomOfStrongTrans (S2130P_fst_site f g T ptA) =
      S2130P_fst f g T ptA from by
        rw [S2130P_fst_site]
        exact S1742HomOfStrongTrans_strongTransOfHom _]
  rw [show S1742HomOfStrongTrans (S2130P_snd_site f g T ptA) =
      S2130P_snd f g T ptA from by
        rw [S2130P_snd_site]
        exact S1742HomOfStrongTrans_strongTransOfHom _]
  change S2130P_fst f g T ptA ≫ S2130Phi f g T ptA =
    S2130P_snd f g T ptA ≫ S2130Graph f g T ptA
  apply Over.OverMorphism.ext
  exact Limits.pullback.condition

noncomputable def S2130Commutes {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2130ToSource f g T ptA) g.map)
      (Pseudofunctor.StrongTrans.vcomp (S2130Proj f g T ptA) (S2130PtC f T ptA)) := by
  let ePhi := (S2130PC f T ptA).isPullback.liftToX
    (schemeRepresentableEtalePseudofunctor S1726K (S2130PB f g T ptA).pullbackScheme)
    (S2130PhiCone f g T ptA)
  let eGraph := (S2130PC f T ptA).isPullback.liftToX
    (schemeRepresentableEtalePseudofunctor S1726K T)
    (S2130GraphCone f g T ptA)
  let eComp := S2130IsoOfHomEq
    (Pseudofunctor.StrongTrans.vcomp (S2130P_fst_site f g T ptA) (S2130PhiSite f g T ptA))
    (Pseudofunctor.StrongTrans.vcomp (S2130P_snd_site f g T ptA) (S2130GraphSite f g T ptA))
    (S2130CompositeHomEq f g T ptA)
  let t1 := S2058AssociatorIso (S2130P_fst_site f g T ptA)
    (S2130PB f g T ptA).toSource g.map
  let t2 := S2058WhiskerLeftIso (S2130P_fst_site f g T ptA)
    (Pseudofunctor.StrongTrans.vcomp (S2130PB f g T ptA).toSource g.map)
    (Pseudofunctor.StrongTrans.vcomp (S2130PhiSite f g T ptA) (S2130PC f T ptA).toSource)
    ePhi.symm
  let t3 := (S2058AssociatorIso (S2130P_fst_site f g T ptA)
    (S2130PhiSite f g T ptA) (S2130PC f T ptA).toSource).symm
  let t4 := S2058WhiskerRightIso
    (Pseudofunctor.StrongTrans.vcomp (S2130P_fst_site f g T ptA) (S2130PhiSite f g T ptA))
    (Pseudofunctor.StrongTrans.vcomp (S2130P_snd_site f g T ptA) (S2130GraphSite f g T ptA))
    (S2130PC f T ptA).toSource eComp
  let t5 := S2058AssociatorIso (S2130P_snd_site f g T ptA)
    (S2130GraphSite f g T ptA) (S2130PC f T ptA).toSource
  let t6 := S2058WhiskerLeftIso (S2130P_snd_site f g T ptA)
    (Pseudofunctor.StrongTrans.vcomp (S2130GraphSite f g T ptA) (S2130PC f T ptA).toSource)
    (S2130PtC f T ptA) eGraph
  exact t1.trans (t2.trans (t3.trans (t4.trans (t5.trans t6))))


noncomputable def S2130ProjectionMap {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    SchemeRepresentableMap (S2130P_snd f g T ptA) where
  transformation := S2130P_snd_site f g T ptA
  app_eq := by
    intro U
    rfl

noncomputable def S2130BaseSquare {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    EtalePseudofunctorSquare
      (schemeRepresentableEtalePseudofunctor S1726K (S2130P f g T ptA))
      B.source.fiber
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber :=
  EtalePseudofunctorSquare.mk (S2130ToSource f g T ptA) (S2130Proj f g T ptA)
    g.map (S2130PtC f T ptA) (S2130Commutes f g T ptA)

def S2130ConcreteTwoPullback : Type _ :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
    (S2130BaseSquare f g T ptA).TwoPullbackWitness

noncomputable def S2130PresentationOfWitness {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (h : (S2130BaseSquare f g T ptA).TwoPullbackWitness) :
    EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA) where
  pullbackScheme := S2130P f g T ptA
  projection := S2130P_snd f g T ptA
  projectionMap := S2130ProjectionMap f g T ptA
  toSource := S2130ToSource f g T ptA
  commutes := S2130Commutes f g T ptA
  isPullback := h

theorem S2130PresentationOfWitness_finiteEtale {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (h : (S2130BaseSquare f g T ptA).TwoPullbackWitness) :
    IsFinite ((S2130PresentationOfWitness f g T ptA h).projection.left) ∧
      Etale ((S2130PresentationOfWitness f g T ptA h).projection.left) :=
  ⟨S2130P_snd_finite f g T ptA, S2130P_snd_etale f g T ptA⟩

noncomputable def S2130ConcreteHgOfTwoPullback (h : S2130ConcreteTwoPullback) :
    ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
      EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA) := by
  intro A B C f g T ptA
  exact S2130PresentationOfWitness f g T ptA (h A B C f g T ptA)

theorem S2130ConcreteHgOfTwoPullback_hasProperty (h : S2130ConcreteTwoPullback) :
    ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
      IsFinite ((S2130ConcreteHgOfTwoPullback h A B C f g T ptA).projection.left) ∧
        Etale ((S2130ConcreteHgOfTwoPullback h A B C f g T ptA).projection.left) := by
  intro A B C f g T ptA
  exact ⟨S2130P_snd_finite f g T ptA, S2130P_snd_etale f g T ptA⟩


def S2130ConcreteButterfly
    (hg : ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
      EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA)) : Type _ :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
    (S2086ToASquare f g T ptA (hg A B C f g T ptA)).TwoPullbackWitness

noncomputable def S2130ToAOfConcreteTwoPullback
    (h : S2130ConcreteTwoPullback)
    (hb : S2130ConcreteButterfly (S2130ConcreteHgOfTwoPullback h)) :
    S2044ToAFiniteEtaleField := by
  change ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.source) (toA f g)
  intro A B C f g
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptA
    exact S2086ToAPresentation f g T ptA
      (S2130ConcreteHgOfTwoPullback h A B C f g T ptA)
      (hb A B C f g T ptA)
  · intro T ptA
    exact S2130ConcreteHgOfTwoPullback_hasProperty h A B C f g T ptA

noncomputable def S2130D6FiniteEtaleOfConcreteTwoPullback
    (h : S2130ConcreteTwoPullback)
    (hb : S2130ConcreteButterfly (S2130ConcreteHgOfTwoPullback h))
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2069D6FiniteEtaleOfToA (S2130ToAOfConcreteTwoPullback h hb) f g

#print axioms S2130Graph_projection
#print axioms S2130Graph_projection_left
#print axioms S2130Graph_open
#print axioms S2130Graph_closed
#print axioms S2130Phi_projection
#print axioms S2130P_snd_eq
#print axioms S2130CompositeHomEq
#print axioms S2130Commutes
#print axioms S2130P_snd_finite
#print axioms S2130P_snd_etale
#print axioms S2130PresentationOfWitness_finiteEtale
#print axioms S2130ConcreteHgOfTwoPullback
#print axioms S2130ConcreteHgOfTwoPullback_hasProperty
#print axioms S2130ToAOfConcreteTwoPullback
#print axioms S2130D6FiniteEtaleOfConcreteTwoPullback

end LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
