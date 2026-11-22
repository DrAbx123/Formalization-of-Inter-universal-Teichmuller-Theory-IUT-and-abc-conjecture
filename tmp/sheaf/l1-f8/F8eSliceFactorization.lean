import F8dThetaProductData

/-!
# F8e — source SliceFactorization obligation

Stage-2 obligation node.  The factorization is not constructed; this file
defines the local `SourceSliceFactorization` predicate and an explicit
obligation over F8a–F8d.  No global object is manufactured by `sorry`.
-/

open CategoryTheory

noncomputable section

namespace SHEAF.L1F8.F8eSliceFactorization

universe u

open LeanFormal.IUT
open Iut.SourceSemiGraphOfAnabelioids
open SHEAF.L1F8.F8aSourceDiagram
open SHEAF.L1F8.F8bSourceYddot
open SHEAF.L1F8.F8cBaseFieldModel
open SHEAF.L1F8.F8dThetaProductData

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- The functorial action of `A ↦ Yddot × A`. -/
def sourceProductMap {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : SourceConnectedTemperedCover diagram root}
    {model : SourceBaseFieldCoverModel diagram root}
    (data : SourceThetaProductData diagram root Yddot model)
    {A B : SourceBaseCover model} (f : A ⟶ B) :
    data.product A ⟶ data.product B :=
  data.lift (data.fst A) (data.snd A ≫ f.hom)

theorem sourceProductMap_fst {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : SourceConnectedTemperedCover diagram root}
    {model : SourceBaseFieldCoverModel diagram root}
    (data : SourceThetaProductData diagram root Yddot model)
    {A B : SourceBaseCover model} (f : A ⟶ B) :
    sourceProductMap data f ≫ data.fst B = data.fst A :=
  data.lift_fst (data.fst A) (data.snd A ≫ f.hom)

/-- The donor `SliceFactorization` predicate for the local product data. -/
def SourceSliceFactorization {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : SourceConnectedTemperedCover diagram root}
    {model : SourceBaseFieldCoverModel diagram root}
    (data : SourceThetaProductData diagram root Yddot model) : Prop :=
  ∀ ⦃A B : SourceBaseCover model⦄
    (h : Over.mk (data.fst A) ⟶ Over.mk (data.fst B)),
    ∃ f : A ⟶ B,
      h = Over.homMk (sourceProductMap data f) (sourceProductMap_fst data f)

/-- F8e obligation: base-field slice factorization over explicit F8a–F8d
obligations. -/
structure SourceSliceFactorizationObligation {xF : Iut.HyperbolicOrbicurve A.F}
    (D : SourceDiagramObligation xF)
    (Y : SourceYddotObligation D)
    (M : SourceBaseFieldModelObligation D Y)
    (P : SourceThetaProductDataObligation D Y M) where
  /-- The factorization proof. -/
  factorization : SourceSliceFactorization P.data

/-- Projection of the factorization field. -/
abbrev SourceSliceFactorizationObligation.factorizationOf
    {xF : Iut.HyperbolicOrbicurve A.F}
    {D : SourceDiagramObligation xF}
    {Y : SourceYddotObligation D}
    {M : SourceBaseFieldModelObligation D Y}
    {P : SourceThetaProductDataObligation D Y M}
    (F : SourceSliceFactorizationObligation D Y M P) :
    SourceSliceFactorization P.data :=
  F.factorization

end SHEAF.L1F8.F8eSliceFactorization