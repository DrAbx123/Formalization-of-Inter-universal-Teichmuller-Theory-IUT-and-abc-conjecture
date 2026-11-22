import F8bSourceYddot

/-!
# F8c — source base-field model obligation

Stage-2 obligation node.  The base-field model is not constructed; this file
defines the local model structure (definitionally the red-donor structure) and
an explicit obligation over F8a/F8b.  No global object is manufactured by
`sorry`.
-/

open CategoryTheory

noncomputable section

namespace SHEAF.L1F8.F8cBaseFieldModel

universe u

open LeanFormal.IUT
open Iut.SourceSemiGraphOfAnabelioids
open SHEAF.L1F8.F8aSourceDiagram
open SHEAF.L1F8.F8bSourceYddot

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- Local reproduction of the donor `BaseFieldCoverModel`. -/
structure SourceBaseFieldCoverModel
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex) where
  /-- Predicate modelling the base-field condition. -/
  IsBaseFieldCover : SourceConnectedTemperedCover diagram root → Prop
  /-- Chosen model of the base object of `B(K_v)^0`. -/
  baseObject : SourceConnectedTemperedCover diagram root
  /-- The base object lies in the base-field full subcategory. -/
  baseObject_mem : IsBaseFieldCover baseObject

/-- The full subcategory of connected tempered covers whose base field is `K_v`. -/
abbrev SourceBaseCover {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} (model : SourceBaseFieldCoverModel diagram root) :=
  ObjectProperty.FullSubcategory model.IsBaseFieldCover

/-- The distinguished base object as an object of `SourceBaseCover`. -/
def sourceBaseCoverObject {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} (model : SourceBaseFieldCoverModel diagram root) :
    SourceBaseCover model :=
  ⟨model.baseObject, model.baseObject_mem⟩

/-- F8c obligation: a base-field model over explicit F8a/F8b obligations. -/
structure SourceBaseFieldModelObligation {xF : Iut.HyperbolicOrbicurve A.F}
    (D : SourceDiagramObligation (l := l) (A := A) xF)
    (Y : SourceYddotObligation (l := l) (A := A) D) where
  /-- The base-field model. -/
  model : SourceBaseFieldCoverModel D.diagram D.root

/-- Projection of the model field. -/
abbrev SourceBaseFieldModelObligation.modelOf {xF : Iut.HyperbolicOrbicurve A.F}
    {D : SourceDiagramObligation (l := l) (A := A) xF}
    {Y : SourceYddotObligation (l := l) (A := A) D}
    (M : SourceBaseFieldModelObligation (l := l) (A := A) D Y) :
    SourceBaseFieldCoverModel D.diagram D.root :=
  M.model

end SHEAF.L1F8.F8cBaseFieldModel