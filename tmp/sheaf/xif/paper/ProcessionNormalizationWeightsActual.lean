import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels

/-!
# Actual procession-normalization weights

This file constructs the actual local normalized weights of IUT III, Remark
3.1.1, (ii), and the actual j in F_l^x procession average of Theorem B /
Corollary 3.12.

Local weights:

  w_w = 1 / [K_w : (F_mod)_v]

are computed from the actual completion algebra of
FinitePlaceCompletionDegree: the local degree is the finrank of the upper
completion over the lower completion, and the weight is its inverse.

The procession average is over the actual label group (ZMod l.value)^x
(F_l^x), with cardinality l - 1, not over the project's SignedLabel (which has
cardinality l and includes 0).

The source V_bad places are abstract in OriginalInput/SourceDefinition31Data.
The actual weights are therefore constructed for every finite place of the
global field; attaching them to the actual V_bad index requires the exact
place-indexing identification recorded as VbadPlaceIndexingObstruction.

No raw SignedLabel sum, no fake weight, no inequality.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators

universe ua uv upi umon ui

/-- The actual local completion degree [K_w : (F_mod)_v] at a finite place w
of the global field K. -/
noncomputable def localCompletionDegree {l : PrimeGeFive}
    (T : InitialThetaArithmeticData l) (w : NumberField.FinitePlace T.K) : Nat :=
  letI : Algebra
      ((comap (k := T.Fmod) w).maximalIdeal.adicCompletion T.Fmod)
      (w.maximalIdeal.adicCompletion T.K) :=
    completionAlgebra (k := T.Fmod) w
  letI : Module.Finite
      ((comap (k := T.Fmod) w).maximalIdeal.adicCompletion T.Fmod)
      (w.maximalIdeal.adicCompletion T.K) :=
    moduleFinite_completionAlgebra (k := T.Fmod) w
  Module.finrank
    ((comap (k := T.Fmod) w).maximalIdeal.adicCompletion T.Fmod)
    (w.maximalIdeal.adicCompletion T.K)

/-- The actual normalized local weight 1/[K_w:(F_mod)_v]. -/
noncomputable def localNormalizedWeight {l : PrimeGeFive}
    (T : InitialThetaArithmeticData l) (w : NumberField.FinitePlace T.K) : Real :=
  ((localCompletionDegree T w : Real))⁻¹

/-- Definitional formula for the local weight. -/
theorem localNormalizedWeight_eq_inv {l : PrimeGeFive}
    (T : InitialThetaArithmeticData l) (w : NumberField.FinitePlace T.K) :
    localNormalizedWeight T w =
      ((Module.finrank
        ((comap (k := T.Fmod) w).maximalIdeal.adicCompletion T.Fmod)
        (w.maximalIdeal.adicCompletion T.K) : Nat) : Real)⁻¹ :=
  rfl

/-- The actual paper label group F_l^x. -/
abbrev ProcessionLabel (l : PrimeGeFive) : Type :=
  (ZMod l.value)ˣ

/-- The actual label cardinality l - 1. -/
theorem processionLabel_card (l : PrimeGeFive) :
    Fintype.card (ProcessionLabel l) = l.value - 1 := by
  haveI : Fact l.value.Prime := ⟨l.prime⟩
  simpa [ProcessionLabel] using ZMod.card_units l.value

/-- The actual uniform procession weight 1/|F_l^x|. -/
def processionLabelWeight (l : PrimeGeFive) : Real :=
  (Fintype.card (ProcessionLabel l) : Real)⁻¹

/-- The actual uniform weights sum to one. -/
theorem processionLabelWeight_total (l : PrimeGeFive) :
    (∑ _j : ProcessionLabel l, processionLabelWeight l) = 1 := by
  haveI : Fact l.value.Prime := ⟨l.prime⟩
  have hcard : (Fintype.card (ProcessionLabel l) : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := ProcessionLabel l)
  rw [Finset.sum_const, nsmul_eq_mul]
  simp [processionLabelWeight, hcard]

/-- The actual F_l^x procession average of a label function. -/
def processionAverage (l : PrimeGeFive) (L : ProcessionLabel l → Real) : Real :=
  ∑ j : ProcessionLabel l, processionLabelWeight l * L j

/-- The actual procession average as division by the label cardinality. -/
theorem processionAverage_eq_sum_div (l : PrimeGeFive)
    (L : ProcessionLabel l → Real) :
    processionAverage l L =
      (∑ j : ProcessionLabel l, L j) /
        (Fintype.card (ProcessionLabel l) : Real) := by
  unfold processionAverage processionLabelWeight
  rw [← Finset.mul_sum]
  ring

/-- Exact source-indexing obstruction: the abstract V_bad index is not
identified with the finite places of the global field. Until this equivalence
(or an equivalent place-selection map) is supplied, the actual local weights
cannot be attached to the actual V_bad elements. -/
def VbadPlaceIndexingObstruction {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (I.initial.badPlaces ≃ NumberField.FinitePlace I.initial.arithmetic.K)

/-- The actual scripted weight structure for a place w: local degree and
normalized inverse weight. -/
structure LocalWeightData {l : PrimeGeFive}
    (T : InitialThetaArithmeticData l) (w : NumberField.FinitePlace T.K) where
  degree : Nat
  degree_eq : degree = localCompletionDegree T w
  weight : Real
  weight_eq : weight = localNormalizedWeight T w

/-- Actual local weight data. -/
def localWeightData {l : PrimeGeFive}
    (T : InitialThetaArithmeticData l) (w : NumberField.FinitePlace T.K) :
    LocalWeightData T w where
  degree := localCompletionDegree T w
  degree_eq := rfl
  weight := localNormalizedWeight T w
  weight_eq := rfl

/-- The exact formula of Remark 3.1.1, (ii): the normalized local weight is the
inverse of the actual completion degree. -/
theorem localWeightData_formula {l : PrimeGeFive}
    (T : InitialThetaArithmeticData l) (w : NumberField.FinitePlace T.K) :
    (localWeightData T w).weight =
      ((localWeightData T w).degree : Real)⁻¹ :=
  rfl

/-- The j in F_l^x average is exactly division by l - 1, not by l and not by a
SignedLabel cardinality. -/
theorem processionAverage_formula (l : PrimeGeFive)
    (L : ProcessionLabel l → Real) :
    processionAverage l L =
      (∑ j : ProcessionLabel l, L j) / (l.value - 1 : Real) := by
  rw [processionAverage_eq_sum_div, processionLabel_card]
  have h1 : 1 ≤ l.value := by
    linarith [l.ge_five]
  rw [Nat.cast_sub h1]
  ring_nf

end LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

end
