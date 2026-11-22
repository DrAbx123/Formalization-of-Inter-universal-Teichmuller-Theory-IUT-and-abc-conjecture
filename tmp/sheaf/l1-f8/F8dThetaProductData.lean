import F8cBaseFieldModel

/-!
# F8d — source Theta product-data obligation

Stage-2 obligation node.  The product data is not constructed; this file
defines the local product-data structure and an explicit obligation over
F8a/F8b/F8c.  No global object is manufactured by `sorry`.
-/

open CategoryTheory

noncomputable section

namespace SHEAF.L1F8.F8dThetaProductData

universe u

open LeanFormal.IUT
open Iut.SourceSemiGraphOfAnabelioids
open SHEAF.L1F8.F8aSourceDiagram
open SHEAF.L1F8.F8bSourceYddot
open SHEAF.L1F8.F8cBaseFieldModel

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- Local reproduction of the donor `ThetaProductData`. -/
structure SourceThetaProductData
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex)
    (Yddot : SourceConnectedTemperedCover diagram root)
    (model : SourceBaseFieldCoverModel diagram root) where
  /-- The product object `Yddot × A`. -/
  product : SourceBaseCover model → SourceConnectedTemperedCover diagram root
  /-- First projection. -/
  fst : ∀ A : SourceBaseCover model, product A ⟶ Yddot
  /-- Second projection. -/
  snd : ∀ A : SourceBaseCover model, product A ⟶ A.obj
  /-- Pairing map into the product. -/
  lift : ∀ {A : SourceBaseCover model} {X : SourceConnectedTemperedCover diagram root},
    (X ⟶ Yddot) → (X ⟶ A.obj) → (X ⟶ product A)
  /-- Pairing is compatible with `fst`. -/
  lift_fst : ∀ {A : SourceBaseCover model} {X : SourceConnectedTemperedCover diagram root}
    (f : X ⟶ Yddot) (g : X ⟶ A.obj), lift (A := A) (X := X) f g ≫ fst A = f
  /-- Pairing is compatible with `snd`. -/
  lift_snd : ∀ {A : SourceBaseCover model} {X : SourceConnectedTemperedCover diagram root}
    (f : X ⟶ Yddot) (g : X ⟶ A.obj), lift (A := A) (X := X) f g ≫ snd A = g
  /-- Uniqueness in the product universal property. -/
  lift_unique : ∀ {A : SourceBaseCover model} {X : SourceConnectedTemperedCover diagram root}
    (f : X ⟶ Yddot) (g : X ⟶ A.obj) (h : X ⟶ product A),
    h ≫ fst A = f → h ≫ snd A = g → h = lift (A := A) (X := X) f g
  /-- The second projection is an epimorphism. -/
  snd_epi : ∀ A : SourceBaseCover model, Epi (snd A)

/-- F8d obligation: product data over explicit F8a/F8b/F8c obligations. -/
structure SourceThetaProductDataObligation {xF : Iut.HyperbolicOrbicurve A.F}
    (D : SourceDiagramObligation (l := l) (A := A) xF)
    (Y : SourceYddotObligation (l := l) (A := A) D)
    (M : SourceBaseFieldModelObligation (l := l) (A := A) D Y) where
  /-- The F8d product data. -/
  data : SourceThetaProductData D.diagram D.root Y.Yddot M.model

/-- Projection of the product-data field. -/
abbrev SourceThetaProductDataObligation.dataOf {xF : Iut.HyperbolicOrbicurve A.F}
    {D : SourceDiagramObligation (l := l) (A := A) xF}
    {Y : SourceYddotObligation (l := l) (A := A) D}
    {M : SourceBaseFieldModelObligation (l := l) (A := A) D Y}
    (P : SourceThetaProductDataObligation (l := l) (A := A) D Y M) :
    SourceThetaProductData D.diagram D.root Y.Yddot M.model :=
  P.data

end SHEAF.L1F8.F8dThetaProductData