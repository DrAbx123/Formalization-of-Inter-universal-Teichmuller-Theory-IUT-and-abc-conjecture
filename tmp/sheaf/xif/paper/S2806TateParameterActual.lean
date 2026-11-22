import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import tmp.sheaf.xif.paper.S2786E37PrimeIdealsActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import tmp.sheaf.xif.paper.S2786SignQuotientActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

local instance s2806GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2806TateParameterActual

variable (w : NumberField.FinitePlace GaussianField)

abbrev v (w : NumberField.FinitePlace GaussianField) := w.maximalIdeal

noncomputable def S2806Q (w : NumberField.FinitePlace GaussianField) : GaussianField :=
  Classical.choose ((v w).valuation_exists_uniformizer GaussianField)

theorem S2806Q_spec (w) :
    (v w).valuation GaussianField (S2806Q w) = WithZero.exp (-1 : Int) :=
  Classical.choose_spec ((v w).valuation_exists_uniformizer GaussianField)

theorem S2806Q_valuation_bridge :
    Valued.v (algebraMap GaussianField ((v w).adicCompletion GaussianField) (S2806Q w)) =
      (v w).valuation GaussianField (S2806Q w) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v w) (S2806Q w)

noncomputable def S2806Candidate : FinitePlaceQCandidate w where
  q := algebraMap GaussianField ((v w).adicCompletion GaussianField) (S2806Q w)
  q_ne_zero := by
    intro hq
    have hzero : Valued.v (algebraMap GaussianField
        ((v w).adicCompletion GaussianField) (S2806Q w)) = 0 := by
      rw [hq]; simp
    rw [S2806Q_valuation_bridge] at hzero
    rw [S2806Q_spec] at hzero
    rw [show (-1 : Int) = -(1 : Int) by norm_num, WithZero.exp_neg] at hzero
    have h1 : WithZero.exp (1 : Int) ≠ 0 := WithZero.exp_ne_zero
    exact (inv_ne_zero h1) hzero
  valuation_lt_one := by
    rw [S2806Q_valuation_bridge]
    rw [S2806Q_spec]
    rw [show (-1 : Int) = -(1 : Int) by norm_num, WithZero.exp_neg]
    have h1 : (1 : WithZero (Multiplicative Int)) < WithZero.exp (1 : Int) := by
      decide
    exact inv_lt_one_of_one_lt₀ h1

theorem S2806Candidate_order :
    (S2806Candidate w).order = 1 := by
  have hv : Valued.v (S2806Candidate w).q = WithZero.exp (-1 : Int) := by
    rw [S2806Candidate, S2806Q_valuation_bridge, S2806Q_spec]
  let h := (S2806Candidate w).valuation_ne_zero
  have hunzero : (WithZero.unzero h).toAdd = (-1 : Int) := by
    rw [WithZero.toAdd_unzero_eq_iff h (-1)]
    simpa [WithZero.exp_eq_coe_ofAdd] using hv
  rw [FinitePlaceQCandidate.order, FinitePlaceQCandidate.exponent]
  change Int.toNat (-(WithZero.unzero h).toAdd) = 1
  rw [hunzero]
  norm_num

theorem S2806Candidate_order_coprime (w : NumberField.FinitePlace GaussianField) :
    Nat.Coprime (S2806Candidate w).order 5 := by
  rw [S2806Candidate_order w]
  norm_num

theorem plus37_order_coprime :
    Nat.Coprime (S2806Candidate gaussianField37PlusPlace).order 5 :=
  S2806Candidate_order_coprime gaussianField37PlusPlace

theorem minus37_order_coprime :
    Nat.Coprime (S2806Candidate gaussianField37MinusPlace).order 5 :=
  S2806Candidate_order_coprime gaussianField37MinusPlace

/-- Realization is the genuine remaining gap: no CurveIndexedTateUniformization
constructor exists.  This Prop records the gap; it is not constructed. -/
def S2806RealizationGap : Prop :=
  forall (w : NumberField.FinitePlace GaussianField),
    Nonempty (CurveIndexedTateUniformization E37QiPunctured w
      (S2806Candidate w))

#check S2806Q
#check S2806Candidate
#print axioms S2806Candidate
#print axioms S2806Candidate_order
#print axioms plus37_order_coprime
#print axioms minus37_order_coprime

end LeanFormal.IUT.XiFPaper.S2806TateParameterActual
end
