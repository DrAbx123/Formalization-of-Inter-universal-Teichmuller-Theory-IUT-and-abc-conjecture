import F8aSourceDiagram
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import Iut.Foundations.SourceTemperedCoveringCategory

/-!
# F8b — source Yddot obligation

Stage-2 obligation node: the distinguished connected tempered cover `Yddot_v` is
not constructed.  This file defines the obligation structure over an explicit
F8a diagram obligation; no global object is manufactured by `sorry`.
-/

noncomputable section

namespace SHEAF.L1F8.F8bSourceYddot

universe u

open CategoryTheory
open LeanFormal.IUT
open Iut.SourceSemiGraphOfAnabelioids
open Iut.SourceSemiGraphOfAnabelioids.CovObject
open SHEAF.L1F8.F8aSourceDiagram

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- Local reproductions of the donor `ConnectedTemperedCover` from the same
production lower module; definitionally equal to the donor abbrev. -/
def sourceConnectedTemperedObjectProperty
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex) :
    ObjectProperty (TemperedCover diagram root) :=
  fun object => AssociatedQuotient.IsGeometricallyConnected object.obj

abbrev SourceConnectedTemperedCover
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex) :=
  (sourceConnectedTemperedObjectProperty diagram root).FullSubcategory

/-- F8b obligation: a distinguished connected tempered cover over an explicit
F8a source diagram and root. -/
structure SourceYddotObligation {xF : Iut.HyperbolicOrbicurve A.F}
    (D : SourceDiagramObligation (l := l) (A := A) xF) where
  /-- The connected tempered cover `Yddot_v`. -/
  Yddot : SourceConnectedTemperedCover D.diagram D.root

/-- Projection of the Yddot field. -/
abbrev SourceYddotObligation.yddotOf {xF : Iut.HyperbolicOrbicurve A.F}
    {D : SourceDiagramObligation (l := l) (A := A) xF}
    (Y : SourceYddotObligation (l := l) (A := A) D) :
    SourceConnectedTemperedCover D.diagram D.root :=
  Y.Yddot

end SHEAF.L1F8.F8bSourceYddot