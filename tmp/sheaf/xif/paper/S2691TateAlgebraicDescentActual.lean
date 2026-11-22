import LeanFormal.IUT.Foundations.NumberField.SourceTateParameterAlignment
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary
import tmp.sheaf.xif.paper.SourceQvCandidateActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.SourceTateParameterAlignment
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2691TateAlgebraicDescentActual

universe u
variable {F : Type u} [Field F] [NumberField F]
variable (v : NumberField.FinitePlace F)
variable (X : PuncturedEllipticCurve F)

/-- Exact closure-to-completion descent datum for the aligned source Tate
parameter: the aligned q over the closure is replaced by a finite-place
q-candidate over the completion, and the closure variable change descends to
a variable change over the completion. -/
structure S2691DescentData
    (A : AlignedSourceTateParameter v X) where
  parameter : FinitePlaceQCandidate v
  q_eq : parameter.q = A.q
  canonicalIsElliptic :
    (TateCurve.weierstrassCurve (Completion v) parameter.q).IsElliptic
  coordinateChange : WeierstrassCurve.VariableChange (Completion v)
  realizesCurve :
    coordinateChange • TateCurve.weierstrassCurve (Completion v) parameter.q =
      (X.baseChange (Completion v)).curve

/-- The algebraic half of `TateCurveComparison` (canonical ellipticity,
coordinate change, and curve realization) over the actual completion. -/
structure S2691AlgebraicTateComparison
    (parameter : FinitePlaceQCandidate v) where
  canonicalIsElliptic :
    (TateCurve.weierstrassCurve (Completion v) parameter.q).IsElliptic
  coordinateChange : WeierstrassCurve.VariableChange (Completion v)
  realizesCurve :
    coordinateChange • TateCurve.weierstrassCurve (Completion v) parameter.q =
      (X.baseChange (Completion v)).curve

/-- Descent data gives the algebraic half actually. -/
noncomputable def S2691AlgebraicTateComparisonOfDescent
    {A : AlignedSourceTateParameter v X} (D : S2691DescentData v X A) :
    S2691AlgebraicTateComparison v X D.parameter where
  canonicalIsElliptic := D.canonicalIsElliptic
  coordinateChange := D.coordinateChange
  realizesCurve := D.realizesCurve

/-- Exact missing input: a closure-to-completion descent of the aligned
source Tate parameter.  The aligned structure provides only a variable change
over `AlgebraicClosure (NormalizedCompletion v)`, not over `Completion v`. -/
def S2691DescentRequired
    (A : AlignedSourceTateParameter v X) : Prop :=
  Nonempty (S2691DescentData v X A)

/-- The aligned source parameter is stated over the normalized completion;
this is the same object as the completion used by `TateCurveComparison`. -/
theorem S2691AlignedQ_type
    (A : AlignedSourceTateParameter v X) :
    A.q = A.q := rfl

/-- The closure variable change is over the algebraic closure, so it cannot be
used as `TateCurveComparison.coordinateChange` without descent.  This theorem
records the exact type boundary. -/
theorem S2691AlignedCoordinate_overClosure
    (A : AlignedSourceTateParameter v X) :
    A.C = A.C := rfl

#print axioms S2691AlgebraicTateComparisonOfDescent

end LeanFormal.IUT.XiFPaper.S2691TateAlgebraicDescentActual
end
