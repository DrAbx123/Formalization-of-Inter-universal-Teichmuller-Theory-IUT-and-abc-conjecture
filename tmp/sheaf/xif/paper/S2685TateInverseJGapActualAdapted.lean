import LeanFormal.IUT.IUTII.Frobenioid.Example36TateInverseJCanonical
import LeanFormal.IUT.Foundations.Geometry.TateInverseJUniformization
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.TateInverseJ
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.NormalizedLogNormComparison
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2685TateInverseJGapActualAdapted

/-- The actual inverse-j data for the concrete split curve at the place above
5: q ≠ 0, q contracting, norm 1/5, and canonical q-series j equal to the
split curve's j. -/
structure S2685InverseJData where
  q : concreteLocalField
  q_ne_zero : q ≠ 0
  q_norm_lt_one : ‖q‖ < 1
  q_norm_eq : ‖q‖ = (5 : ℝ)⁻¹
  q_canonicalJ : canonicalQSeriesJ q = concreteSplitCurveLocal.j

noncomputable def S2685InverseJData.ofExistence : S2685InverseJData := by
  obtain ⟨q, _hH, hcanon, hqne, hq1, hnorm, _hdist⟩ :=
    exists_canonicalQSeriesJ_eq_split_j_full
  exact ⟨q, hqne, hq1, hnorm, hcanon⟩

noncomputable def S2685Data : S2685InverseJData :=
  S2685InverseJData.ofExistence

/-- The actual inverse-j parameter packaged as a finite-place q-candidate. -/
noncomputable def S2685InverseJParameterCandidate :
    NumberFieldFinitePlace.FinitePlaceQCandidate concreteFivePlace :=
  { q := S2685Data.q
    q_ne_zero := S2685Data.q_ne_zero
    valuation_lt_one := (norm_lt_one_iff_valued_lt_one S2685Data.q).mp
      S2685Data.q_norm_lt_one }

@[simp] theorem S2685InverseJParameterCandidate_q :
    S2685InverseJParameterCandidate.q = S2685Data.q := rfl

theorem S2685ParameterCandidate_norm :
    ‖(S2685InverseJParameterCandidate).q‖ = (5 : ℝ)⁻¹ := by
  rw [S2685InverseJParameterCandidate_q]
  exact S2685Data.q_norm_eq

theorem S2685ParameterCandidate_inverseJ :
    canonicalQSeriesJ (S2685InverseJParameterCandidate).q =
      concreteSplitCurveLocal.j := by
  rw [S2685InverseJParameterCandidate_q]
  exact S2685Data.q_canonicalJ

/-- The exact remaining analytic API: a curve-indexed Tate uniformization at
the actual inverse-j parameter candidate.  This is the only missing input of
`TateInverseJUniformizationInterface` once the inverse-j parameter is packaged. -/
def S2685MissingCurveUniformization : Prop :=
  Nonempty (CurveIndexedTateUniformization concreteSplitPuncturedCurve
    concreteFivePlace S2685InverseJParameterCandidate)

theorem S2685TateInverseJInterface_of_uniformization
    (h : S2685MissingCurveUniformization) :
    TateInverseJUniformizationInterface :=
  ⟨S2685InverseJParameterCandidate, h, S2685ParameterCandidate_norm⟩

theorem S2685TateInverseJInterface_uniformization
    (h : TateInverseJUniformizationInterface) :
    ∃ (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate concreteFivePlace),
      Nonempty (CurveIndexedTateUniformization concreteSplitPuncturedCurve
        concreteFivePlace parameter) ∧ ‖parameter.q‖ = (5 : ℝ)⁻¹ :=
  h

#check S2685InverseJParameterCandidate
#check S2685ParameterCandidate_norm
#check S2685ParameterCandidate_inverseJ
#check S2685MissingCurveUniformization
#check S2685TateInverseJInterface_of_uniformization
#print axioms S2685ParameterCandidate_norm
#print axioms S2685ParameterCandidate_inverseJ
#print axioms S2685TateInverseJInterface_of_uniformization

end LeanFormal.IUT.XiFPaper.S2685TateInverseJGapActualAdapted
end