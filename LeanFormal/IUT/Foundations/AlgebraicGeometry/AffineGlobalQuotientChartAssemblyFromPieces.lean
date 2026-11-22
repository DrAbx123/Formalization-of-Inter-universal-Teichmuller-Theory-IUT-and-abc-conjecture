import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalGluedQuotientAssembly
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPieceIdentification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGlobalQuotientChartAssemblyFromPieces

universe u

variable {S : Scheme.{u}}

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalGluedQuotientAssembly
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPieceIdentification
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-- The affine chart assembly carried by a global quotient chart presentation. -/
noncomputable def ofChartPresentation
    (D : GlobalQuotientChartPresentation S) :
    AffineGlobalQuotientChartAssembly S where
  J := D.P.J
  U := D.P.U
  V := D.P.V
  f := D.P.f
  f_open := D.P.f_open
  f_hasPullback := D.P.f_hasPullback
  f_id := D.P.f_id
  t := D.P.t
  t_id := D.P.t_id
  t' := D.P.t'
  t_fac := D.P.t_fac
  cocycle := D.P.cocycle
  q := D.P.q
  q_etale := D.P.q_etale

/-- The chart assembly from the affine quotient-piece cover and the chart presentation.
The cover supplies the affine pieces; the presentation supplies the actual gluing data. -/
noncomputable def ofPiecesAndChartPresentation
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {G : Type u} [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G))
    (D : GlobalQuotientChartPresentation S) :
    AffineGlobalQuotientChartAssembly S :=
  ofChartPresentation D

/-- The assembly's chart affine and etale fields are inherited from the chart
presentation. -/
theorem ofChartPresentation_chart_affine
    (D : GlobalQuotientChartPresentation S) (i : D.P.J) :
    IsAffine ((ofChartPresentation D).U i) :=
  D.chartAffine i

theorem ofChartPresentation_chart_etale
    (D : GlobalQuotientChartPresentation S) (i : D.P.J) :
    Etale ((ofChartPresentation D).q i) :=
  D.chartEtale i

/-- The chart assembly gives the preglue data consumed by the global assembly. -/
noncomputable def ofChartPresentation_toPreglueData
    (D : GlobalQuotientChartPresentation S) :
    LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct.AffineLocalQuotientPreglueData S :=
  (ofChartPresentation D).toPreglueData

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGlobalQuotientChartAssemblyFromPieces
