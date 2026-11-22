import tmp.sheaf.xif.paper.S3029StepVAlignmentActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual

universe u v w

/-- The label-independent unit of the StepV term:
`-(-ord J)/(2l) * log p`. -/
noncomputable def S3050Unit {K : Type u} [Norm K] (p : Nat)
    (jValue : K) (l : Nat) : Real :=
  -((-localNormOrder p jValue) / (2 * l : Nat)) * Real.log (p : Real)

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (l : Nat)

/-- Exact expansion of StepVTerm as label^2 times a label-independent unit. -/
theorem S3050_stepVTerm_eq_label_sq_mul_unit (label : Nat) :
    S3029StepVTerm places tuple istar jValue l label =
      (label : Real) ^ 2 * S3050Unit p jValue l := by
  unfold S3029StepVTerm stepVLambda S3050Unit
  ring

/-- Coefficient of Q in the label^2 affine form. -/
noncomputable def S3050QCoeff (label : Nat) : Real :=
  (label : Real) ^ 2

/-- Residual after subtracting `label^2 * Q`: it absorbs the mismatch
between the StepV unit and the chosen S2921 Q. -/
noncomputable def S3050LabelRest (Q : Real) (label : Nat) : Real :=
  (label : Real) ^ 2 * (S3050Unit p jValue l - Q)

/-- Exact affine decomposition in an arbitrary chosen Q. -/
theorem S3050_stepVTerm_eq_qCoeff_mul_Q_add_rest
    (Q : Real) (label : Nat) :
    S3029StepVTerm places tuple istar jValue l label =
      S3050QCoeff label * Q + S3050LabelRest places tuple istar jValue l Q label := by
  rw [S3050_stepVTerm_eq_label_sq_mul_unit]
  unfold S3050QCoeff S3050LabelRest
  ring

/-- Exact missing identification: the StepV unit must be a fixed multiple of
the chosen S2921 Q. -/
def S3050QUnitIdentification (Q : Real) : Prop :=
  exists c : Real, S3050Unit p jValue l = c * Q

#check S3050Unit
#check S3050_stepVTerm_eq_label_sq_mul_unit
#check S3050QCoeff
#check S3050LabelRest
#check S3050_stepVTerm_eq_qCoeff_mul_Q_add_rest
#check S3050QUnitIdentification
#print axioms S3050_stepVTerm_eq_label_sq_mul_unit
#print axioms S3050_stepVTerm_eq_qCoeff_mul_Q_add_rest

end LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual
end