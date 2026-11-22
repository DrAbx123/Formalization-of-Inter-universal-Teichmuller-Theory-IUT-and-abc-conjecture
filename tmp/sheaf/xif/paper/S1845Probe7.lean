import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import Mathlib.AlgebraicGeometry.Limits
set_option pp.all true
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

#check @CategoryTheory.Functor.ext
example (F G : CategoryTheory.Functor (Discrete (Fin 2)) (Discrete (Fin 3)))
    (h : ∀ X, F.obj X = G.obj X) : F = G := by
  refine CategoryTheory.Functor.ext h ?_
  intro X Y f
  trace_state
  exact Subsingleton.elim _ _
