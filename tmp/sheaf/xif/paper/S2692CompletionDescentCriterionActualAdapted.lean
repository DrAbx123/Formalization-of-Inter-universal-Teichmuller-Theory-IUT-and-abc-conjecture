import tmp.sheaf.xif.paper.S2691TateAlgebraicDescentActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.SourceTateParameterAlignment
open LeanFormal.IUT.XiFPaper.S2691TateAlgebraicDescentActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2692CompletionDescentCriterionActualAdapted

universe u
variable {F : Type u} [Field F] [NumberField F]
variable (v : NumberField.FinitePlace F)
variable (X : PuncturedEllipticCurve F)

/-- Exact feasible condition: the two curves are already isomorphic over the
completion, i.e. there is a variable change over `Completion v` from the
canonical Tate curve to the base-changed local curve. -/
def S2692CurvesIsomorphicOverCompletion
    (parameter : FinitePlaceQCandidate v) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange (Completion v),
    C • TateCurve.weierstrassCurve (Completion v) parameter.q =
      (X.baseChange (Completion v)).curve

/-- An actual algebraic half supplies a completion variable change. -/
theorem S2692AlgebraicHalf_implies_isomorphic
    (parameter : FinitePlaceQCandidate v)
    (h : Nonempty (S2691AlgebraicTateComparison v X parameter)) :
    S2692CurvesIsomorphicOverCompletion v X parameter := by
  rcases h with ⟨A⟩
  exact ⟨A.coordinateChange, A.realizesCurve⟩

/-- Feasible special case: if the base-changed local curve is literally the
canonical Tate curve, the identity variable change gives the algebraic half. -/
theorem S2692AlgebraicHalf_of_curve_eq
    (parameter : FinitePlaceQCandidate v)
    (h : (X.baseChange (Completion v)).curve =
      TateCurve.weierstrassCurve (Completion v) parameter.q)
    (hcanon : (TateCurve.weierstrassCurve (Completion v) parameter.q).IsElliptic) :
    S2691AlgebraicTateComparison v X parameter where
  canonicalIsElliptic := hcanon
  coordinateChange := 1
  realizesCurve := by
    rw [one_smul]
    exact h.symm

/-- Exact infeasibility formulation: the alignment gives a variable change
only after scalar extension to the algebraic closure.  Its closure C cannot be
used as a completion C without proving base-field descent. -/
def S2692ClosureDescentGap
    (A : AlignedSourceTateParameter v X) : Prop :=
  S2691DescentRequired v X A

theorem S2692Alignment_closure_only
    (A : AlignedSourceTateParameter v X) :
    A.C = A.C := rfl

#print axioms S2692AlgebraicHalf_of_curve_eq

end LeanFormal.IUT.XiFPaper.S2692CompletionDescentCriterionActualAdapted
end
