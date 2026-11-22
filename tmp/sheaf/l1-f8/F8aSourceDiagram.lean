import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import Iut.Foundations.SourceSemiGraphOfAnabelioids

/-!
# F8a — source semi-graph diagram obligation

Stage-2 statement node: the source semi-graph of anabelioids and its marked root
vertex are not constructed.  This file only defines the obligation structure and
projections from it; no global object is manufactured by `sorry`.
-/

noncomputable section

namespace SHEAF.L1F8.F8aSourceDiagram

universe u

open LeanFormal.IUT

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- Obligation for F8a: the source semi-graph of anabelioids attached to an
actual source orbicurve and its chosen root vertex.  An inhabitant must be
supplied by the source-geometry node; this file does not construct one. -/
structure SourceDiagramObligation (xF : Iut.HyperbolicOrbicurve A.F) where
  /-- The source semi-graph of anabelioids attached to `xF`. -/
  diagram : Iut.SourceSemiGraphOfAnabelioids.{u}
  /-- The marked root vertex of the diagram. -/
  root : diagram.base.Vertex

/-- Projection of the diagram field. -/
abbrev SourceDiagramObligation.diagramOf {xF : Iut.HyperbolicOrbicurve A.F}
    (D : SourceDiagramObligation (l := l) (A := A) xF) :
    Iut.SourceSemiGraphOfAnabelioids.{u} :=
  D.diagram

/-- Projection of the root field. -/
abbrev SourceDiagramObligation.rootOf {xF : Iut.HyperbolicOrbicurve A.F}
    (D : SourceDiagramObligation (l := l) (A := A) xF) :
    D.diagram.base.Vertex :=
  D.root

end SHEAF.L1F8.F8aSourceDiagram