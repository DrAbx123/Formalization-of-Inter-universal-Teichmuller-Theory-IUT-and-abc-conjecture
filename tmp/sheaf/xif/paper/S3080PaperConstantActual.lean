import tmp.sheaf.xif.paper.S3079PaperAlignmentQCoeffActual
import tmp.sheaf.xif.paper.S2967QDecomposition

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3079PaperAlignmentQCoeffActual
open LeanFormal.IUT.XiFPaper.S2967QDecomposition
open LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3080PaperConstantActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (l : Nat)

theorem S3080_coeff_eq_iff
    (hu : S3050Unit p jValue l ≠ 0) {Q1 Q2 : Real} :
    S3079QCoeff places tuple istar jValue l Q1 =
      S3079QCoeff places tuple istar jValue l Q2 ↔ Q1 = Q2 := by
  constructor
  · intro h
    by_cases h1 : Q1 = 0
    · subst Q1
      by_cases h2 : Q2 = 0
      · exact h2.symm
      · exfalso
        have h0 : S3079QCoeff places tuple istar jValue l 0 = 0 := by
          unfold S3079QCoeff; simp
        rw [h0] at h
        have hne : S3079QCoeff places tuple istar jValue l Q2 ≠ 0 := by
          unfold S3079QCoeff
          exact div_ne_zero hu h2
        exact hne h.symm
    · by_cases h2 : Q2 = 0
      · exfalso
        subst Q2
        have h0 : S3079QCoeff places tuple istar jValue l 0 = 0 := by
          unfold S3079QCoeff; simp
        rw [h0] at h
        have hne : S3079QCoeff places tuple istar jValue l Q1 ≠ 0 := by
          unfold S3079QCoeff
          exact div_ne_zero hu h1
        exact hne h
      · unfold S3079QCoeff at h
        field_simp [h1, h2] at h
        exact h.symm
  · intro h
    rw [h]

theorem S3080_unit_ne_zero (hp : Nat.Prime p) (hl : 0 < l)
    (hord : localNormOrder p jValue ≠ 0) :
    S3050Unit p jValue l ≠ 0 := by
  unfold S3050Unit
  have hlog : Real.log (p : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast hp.pos
    · intro h
      have : p = 1 := by exact_mod_cast h
      exact hp.ne_one this
  have hden : (2 * (l : Real)) ≠ 0 := by positivity
  have hord' : -localNormOrder p jValue ≠ 0 := neg_ne_zero.mpr hord
  field_simp [hlog, hden, hord']
  exact div_ne_zero (mul_ne_zero hord hlog) (by positivity)

def S3080TripleIndependent
    (Qfun : Nat -> Nat -> Nat -> Real) : Prop :=
  exists c : Real, forall a b c3 : Nat,
    S3079QCoeff places tuple istar jValue l (Qfun a b c3) = c

theorem S3080_not_tripleIndependent_of_Q_diff
    (hu : S3050Unit p jValue l ≠ 0)
    (Qfun : Nat -> Nat -> Nat -> Real)
    (h : exists a1 b1 c1 a2 b2 c2 : Nat,
      Qfun a1 b1 c1 ≠ Qfun a2 b2 c2) :
    ¬ S3080TripleIndependent places tuple istar jValue l Qfun := by
  rintro ⟨c, hc⟩
  obtain ⟨a1, b1, c1, a2, b2, c2, hne⟩ := h
  have heq : Qfun a1 b1 c1 = Qfun a2 b2 c2 := by
    have h1 := hc a1 b1 c1
    have h2 := hc a2 b2 c2
    exact (S3080_coeff_eq_iff places tuple istar jValue l hu).mp (h1.trans h2.symm)
  exact hne heq

#check S3080_coeff_eq_iff
#check S3080_unit_ne_zero
#check S3080TripleIndependent
#check S3080_not_tripleIndependent_of_Q_diff
#print axioms S3080_coeff_eq_iff
#print axioms S3080_unit_ne_zero
#print axioms S3080_not_tripleIndependent_of_Q_diff

end LeanFormal.IUT.XiFPaper.S3080PaperConstantActual
end
