import tmp.sheaf.xif.paper.S3128TerminalCoverActual
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3128TerminalCoverActual
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
noncomputable section
variable {l : PrimeGeFive}
example : HasPullbacks (SchemeOverField (S1348K l)) := inferInstance
