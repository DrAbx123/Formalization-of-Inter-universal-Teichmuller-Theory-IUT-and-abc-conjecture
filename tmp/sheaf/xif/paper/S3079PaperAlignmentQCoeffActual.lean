import tmp.sheaf.xif.paper.S3050StepVQExpansionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3079PaperAlignmentQCoeffActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (l : Nat)

/-- The exact required proportionality constant of the StepV unit over Q. -/
noncomputable def S3079QCoeff (Q : Real) : Real :=
  S3050Unit p jValue l / Q

theorem S3079_unit_eq_coeff_mul_Q {Q : Real} (hQ : Q ≠ 0) :
    S3050Unit p jValue l = S3079QCoeff places tuple istar jValue l Q * Q := by
  unfold S3079QCoeff
  field_simp [hQ]

/-- With `c = unit/Q`, the StepV term is exactly `label² * c * Q`,
with zero remainder. -/
theorem S3079_stepVTerm_eq_qCoeff_mul_Q (Q : Real) (hQ : Q ≠ 0) (label : Nat) :
    S3029StepVTerm places tuple istar jValue l label =
      ((label : Real) ^ 2 * S3079QCoeff places tuple istar jValue l Q) * Q := by
  rw [S3050_stepVTerm_eq_label_sq_mul_unit]
  have h := S3079_unit_eq_coeff_mul_Q (places := places) (tuple := tuple)
    (istar := istar) (jValue := jValue) (l := l) (Q := Q) hQ
  rw [h]
  ring

/-- The exact missing paper normalization: the per-triple constant
`unit/Q` must equal a triple-independent paper constant. -/
def S3079PaperConstantTarget (Qfun : Nat -> Nat -> Nat -> Real) : Prop :=
  exists c : Real,
    forall a b c₃ : Nat,
      S3079QCoeff places tuple istar jValue l (Qfun a b c₃) = c

#check S3079QCoeff
#check S3079_unit_eq_coeff_mul_Q
#check S3079_stepVTerm_eq_qCoeff_mul_Q
#check S3079PaperConstantTarget
#print axioms S3079_unit_eq_coeff_mul_Q
#print axioms S3079_stepVTerm_eq_qCoeff_mul_Q

end LeanFormal.IUT.XiFPaper.S3079PaperAlignmentQCoeffActual
end