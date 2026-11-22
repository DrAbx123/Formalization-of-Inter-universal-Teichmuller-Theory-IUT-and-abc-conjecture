import tmp.sheaf.xif.paper.S2441C9PaperCarrierActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual

/-! # S2448: general normalization skeleton and concrete 2l obstruction

Actual concrete bad-place map and root-factor algebra; the 2l-corrected
candidate is separated from the raw source sum and their inequality is proved.
The general paper normalization (local weights, 1/[F:Q], procession average,
literal O^▷ generators) is recorded as exact missing, not assumed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open CategoryTheory IsDedekindDomain NumberField
open scoped BigOperators
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S1979QPilotStripFromDivisorActual
open LeanFormal.IUT.XiFPaper.S2441C9PaperCarrierActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

local instance s2448GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2448FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S2448GeneralNormalizationActual

/-- Actual bad-place map for the S1895 concrete input. -/
structure S2448BadPlaceMap (D : S1895PaperInput) where
  place : (paperInput D).initial.badPlaces →
    HeightOneSpectrum (NumberField.RingOfIntegers (PaperFmod D))
  place_eq : ∀ b, place b = paperBadBasePlace D b
  q_v : (paperInput D).initial.badPlaces → Real
  q_v_eq : ∀ b, q_v b = paperQV D b
  order : (paperInput D).initial.badPlaces → Nat
  order_eq : ∀ b, order b = paperQVOrder D b
  residueWeight : (paperInput D).initial.badPlaces → Real
  residueWeight_eq : ∀ b, residueWeight b = Real.log 5

noncomputable def s2448BadPlaceMap (D : S1895PaperInput) :
    S2448BadPlaceMap D where
  place := paperBadBasePlace D
  place_eq := fun _ => rfl
  q_v := paperQV D
  q_v_eq := fun _ => rfl
  order := paperQVOrder D
  order_eq := fun _ => rfl
  residueWeight := fun _ => Real.log 5
  residueWeight_eq := fun _ => rfl

/-- The IUT-IV root factor `1/(2l)`. -/
noncomputable def paperRootFactor (l : PrimeGeFive) : Real :=
  (2 * (l.value : Real))⁻¹

theorem paperRootFactor_mul_two_l (l : PrimeGeFive) :
    paperRootFactor l * (2 * (l.value : Real)) = 1 := by
  unfold paperRootFactor
  have hl : (l.value : Real) ≠ 0 :=
    by exact_mod_cast Nat.ne_of_gt (Nat.Prime.pos l.prime)
  field_simp

/-- The 2l-corrected candidate for the paper scalar. -/
noncomputable def paperTwoLCorrectedCandidate (D : S1895PaperInput) : Real :=
  paperRootFactor D.l * sourceQPilotSignedLog (paperInput D).initial

theorem s2448_twoLCorrected_eq (D : S1895PaperInput) :
    paperTwoLCorrectedCandidate D =
      -((S1487Cand.order : Real) * Real.log 5 /
        (2 * (D.l.value : Real))) := by
  unfold paperTwoLCorrectedCandidate paperRootFactor
  rw [s2441_concrete_normalization D]
  ring

/-- The raw source sum is not the 2l-corrected candidate for l ≥ 5. -/
theorem s2448_raw_ne_twoLCorrected (D : S1895PaperInput) :
    sourceQPilotSignedLog (paperInput D).initial ≠
      paperTwoLCorrectedCandidate D := by
  intro h
  have hsrc := s2441_concrete_normalization D
  have hcorr := s2448_twoLCorrected_eq D
  have hlog : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have horder : 0 < (S1487Cand.order : Real) :=
    by exact_mod_cast S1487Cand.order_pos
  have hC : 0 < (S1487Cand.order : Real) * Real.log 5 :=
    mul_pos horder hlog
  have hl : 1 < 2 * (D.l.value : Real) := by
    have hge : (5 : Real) ≤ (D.l.value : Real) := by
      exact_mod_cast D.l.ge_five
    nlinarith
  have h1 : -((S1487Cand.order : Real) * Real.log 5) =
      -((S1487Cand.order : Real) * Real.log 5 /
        (2 * (D.l.value : Real))) := by
    rw [← s2441_concrete_normalization D, h, s2448_twoLCorrected_eq D]
  have h2 : (S1487Cand.order : Real) * Real.log 5 =
      (S1487Cand.order : Real) * Real.log 5 /
        (2 * (D.l.value : Real)) := by linarith
  have hden : (2 * (D.l.value : Real)) ≠ 0 := by nlinarith
  have h3 : ((S1487Cand.order : Real) * Real.log 5) *
      (2 * (D.l.value : Real)) =
        (S1487Cand.order : Real) * Real.log 5 := by
    calc ((S1487Cand.order : Real) * Real.log 5) *
          (2 * (D.l.value : Real)) =
        (((S1487Cand.order : Real) * Real.log 5) /
          (2 * (D.l.value : Real))) * (2 * (D.l.value : Real)) := by
          conv_lhs => rw [h2]
      _ = ((S1487Cand.order : Real) * Real.log 5) :=
          div_mul_cancel₀ _ hden
  have h4 : (2 * (D.l.value : Real)) = 1 := by
    apply mul_left_cancel₀ (ne_of_gt hC)
    calc ((S1487Cand.order : Real) * Real.log 5) *
          (2 * (D.l.value : Real)) =
        (S1487Cand.order : Real) * Real.log 5 := h3
      _ = ((S1487Cand.order : Real) * Real.log 5) * 1 := by ring
  nlinarith

/-- General paper normalization exact missing (no inhabitant). -/
structure S2448GeneralNormalizationRequired (D : S1895PaperInput) where
  badPlaceMap : S2448BadPlaceMap D
  rootFactor : Real
  rootFactor_eq : rootFactor = paperRootFactor D.l
  finrank_eq_two : Module.finrank ℚ (PaperFmod D) = 2
  normalizedDegree : Real
  normalizedDegree_eq :
    normalizedDegree =
      (Module.finrank ℚ (PaperFmod D) : Real)⁻¹ *
        IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D)
  localWeights : (paperInput D).initial.badPlaces → Real
  localWeights_eq : ∀ b, localWeights b = Real.log 5
  processionAverage : Real
  paperNormalized : Real
  paperNormalized_eq : paperNormalized = -rootFactor * normalizedDegree
  candidate_eq_paper :
    sourceQPilotSignedLog (paperInput D).initial = paperNormalized

#check S2448BadPlaceMap
#check s2448BadPlaceMap
#check paperRootFactor_mul_two_l
#check s2448_twoLCorrected_eq
#check s2448_raw_ne_twoLCorrected
#check S2448GeneralNormalizationRequired

end LeanFormal.IUT.XiFPaper.S2448GeneralNormalizationActual
end
