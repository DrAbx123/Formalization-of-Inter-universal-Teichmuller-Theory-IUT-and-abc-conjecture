/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1QOrderOneActual
import tmp.sheaf.xif.paper.S2806TateParameterActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import Mathlib.Tactic

/-! # Mzk1TateUniformizerConstructionActual — A793 (qpilot)

Question: can we construct a uniformizer witness for
`SourceTateComparisonWitness` (so that `order = 1`)?

Results:
1. **Candidate**: for *any* number field `K` and finite place `w`, an order-1
   `FinitePlaceQCandidate` is constructed from an actual uniformizer of the place
   (generalizing `S2806TateParameterActual.S2806Candidate` from the Gaussian field):
   `uniformizerCandidate w`, `uniformizerCandidate_order : order = 1`.
2. **Witness (conditional)**: `SourceTateComparisonWitness` with this uniformizer
   parameter is constructed as soon as a `TateCurveComparison A.curve w` for that
   parameter is supplied (`uniformizerWitness`); its order is 1 and coprimality holds.
3. **Clause B (conditional)**: from a family of such comparisons one gets
   `BadPlaceTateUniformizationCards` with all parameters uniformizers, hence a
   clause-B record via the existing `sourceClauseB_of_tateUniformizationCards`.
4. **`qVFamily` relation**: `qVFamily` is `Classical.choice` of the clause-B
   `Nonempty`; `Classical.choice` does not reduce (no `choice_eq` for `Nonempty`),
   so the order of `qVFamily T b` cannot be transported from a constructed witness.
   Correct usages: (i) add `TateUniformizerCondition` (exponent = 1) to the actual
   `qVFamily`, or (ii) use an explicit-witness variant of the definition.  The exact
   remaining mathematical gap is the Tate realization (`TateCurveComparison`), not the
   valuation order: vendor `TateCurvesTheta` proves the normalized-order side, and
   `S2806RealizationGap` records the realization gap.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TateUniformizerConstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1QOrderOneActual
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.InitialThetaSource.SourceTateComparisonWitness

universe u

/-! ### 1. Uniformizer q-candidate for an arbitrary number-field place -/

section UniformizerCandidate

variable {K : Type u} [Field K] [NumberField K]

abbrev placeMaximalIdeal (w : NumberField.FinitePlace K) :=
  w.maximalIdeal

/-- The actual uniformizer element at the place (Mathlib height-one spectrum). -/
noncomputable def uniformizerQ (w : NumberField.FinitePlace K) : K :=
  Classical.choose ((placeMaximalIdeal w).valuation_exists_uniformizer K)

theorem uniformizerQ_spec (w : NumberField.FinitePlace K) :
    (placeMaximalIdeal w).valuation K (uniformizerQ w) = WithZero.exp (-1 : Int) :=
  Classical.choose_spec ((placeMaximalIdeal w).valuation_exists_uniformizer K)

theorem uniformizerQ_valuation_bridge (w : NumberField.FinitePlace K) :
    Valued.v (algebraMap K ((placeMaximalIdeal w).adicCompletion K) (uniformizerQ w)) =
      (placeMaximalIdeal w).valuation K (uniformizerQ w) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (placeMaximalIdeal w) (uniformizerQ w)

/-- The uniformizer gives an order-1 q-parameter candidate at the place. -/
noncomputable def uniformizerCandidate (w : NumberField.FinitePlace K) :
    FinitePlaceQCandidate w where
  q := algebraMap K ((placeMaximalIdeal w).adicCompletion K) (uniformizerQ w)
  q_ne_zero := by
    intro hq
    have hzero : Valued.v (algebraMap K
        ((placeMaximalIdeal w).adicCompletion K) (uniformizerQ w)) = 0 := by
      rw [hq]; simp
    rw [uniformizerQ_valuation_bridge] at hzero
    rw [uniformizerQ_spec] at hzero
    rw [show (-1 : Int) = -(1 : Int) by norm_num, WithZero.exp_neg] at hzero
    have h1 : WithZero.exp (1 : Int) ≠ 0 := WithZero.exp_ne_zero
    exact (inv_ne_zero h1) hzero
  valuation_lt_one := by
    rw [uniformizerQ_valuation_bridge]
    rw [uniformizerQ_spec]
    rw [show (-1 : Int) = -(1 : Int) by norm_num, WithZero.exp_neg]
    have h1 : (1 : WithZero (Multiplicative Int)) < WithZero.exp (1 : Int) := by
      decide
    exact inv_lt_one_of_one_lt₀ h1

theorem uniformizerCandidate_order (w : NumberField.FinitePlace K) :
    (uniformizerCandidate w).order = 1 := by
  have hv : Valued.v (uniformizerCandidate w).q = WithZero.exp (-1 : Int) := by
    rw [uniformizerCandidate, uniformizerQ_valuation_bridge, uniformizerQ_spec]
  let h := (uniformizerCandidate w).valuation_ne_zero
  have hunzero : (WithZero.unzero h).toAdd = (-1 : Int) := by
    rw [WithZero.toAdd_unzero_eq_iff h (-1)]
    simpa [WithZero.exp_eq_coe_ofAdd] using hv
  rw [FinitePlaceQCandidate.order, FinitePlaceQCandidate.exponent]
  change Int.toNat (-(WithZero.unzero h).toAdd) = 1
  rw [hunzero]
  norm_num

theorem uniformizerCandidate_order_coprime (w : NumberField.FinitePlace K)
    {l : PrimeGeFive} : Nat.Coprime (uniformizerCandidate w).order l.value := by
  rw [uniformizerCandidate_order]
  exact Nat.coprime_one_left l.value

end UniformizerCandidate

/-! ### 2. Conditional witness with uniformizer parameter -/

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData l}

/-- With a Tate realization for the uniformizer candidate, the clause-B witness has
`parameter = uniformizerCandidate` and order 1. -/
noncomputable def uniformizerWitness (w : NumberField.FinitePlace A.F)
    (comparison : TateCurveComparison A.curve w (uniformizerCandidate w)) :
    SourceTateComparisonWitness A w :=
  SourceTateComparisonWitness.ofComparison (uniformizerCandidate w) comparison
    (uniformizerCandidate_order_coprime w)

theorem uniformizerWitness_parameter (w : NumberField.FinitePlace A.F)
    (comparison : TateCurveComparison A.curve w (uniformizerCandidate w)) :
    (uniformizerWitness w comparison).parameter = uniformizerCandidate w :=
  rfl

theorem uniformizerWitness_order (w : NumberField.FinitePlace A.F)
    (comparison : TateCurveComparison A.curve w (uniformizerCandidate w)) :
    (uniformizerWitness w comparison).parameter.order = 1 :=
  uniformizerCandidate_order w

/-! ### 3. Conditional clause-B construction with all parameters uniformizers -/

variable {S : SourceSignQuotientData A}
variable {CA : SourceClauseA A S}

/-- Uniformizer comparison cards for a place selection: all parameters are the
constructed uniformizer candidates and all orders are 1. -/
noncomputable def uniformizerComparisonCards
    (P : SourcePlaceSelection A)
    (comparison : ∀ (w : NumberField.FinitePlace A.F)
      (_hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      TateCurveComparison A.curve w (uniformizerCandidate w)) :
    BadPlaceTateUniformizationCards P where
  parameter := fun w _ => uniformizerCandidate w
  comparison := comparison
  order_coprime := fun w _ => uniformizerCandidate_order_coprime w

/-- Clause B assembled from uniformizer comparisons (conditional on the Tate
realizations, the multiplicative-reduction function and residue coprimality). -/
theorem clauseB_of_uniformizerComparisons
    (P : SourcePlaceSelection A)
    (hV_mod_bad : S.V_mod_bad = P.V_mod_bad)
    (multiplicative : ∀ w : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ S.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt w)
    (comparison : ∀ (w : NumberField.FinitePlace A.F)
      (_hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      TateCurveComparison A.curve w (uniformizerCandidate w))
    (residueCoprime : ∀ w : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ S.V_mod_bad →
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) w))) :
    SourceClauseB A S CA :=
  sourceClauseB_of_tateUniformizationCards P hV_mod_bad multiplicative
    (uniformizerComparisonCards P comparison) residueCoprime

/-! ### 4. `qVFamily` and `Classical.choice` obstruction -/

variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- On a clause B built from uniformizer comparisons, `qVFamily` is the parameter of
the *chosen* witness; `Classical.choice` does not reduce. -/
theorem qVFamily_choice_form :
    qVFamily T b =
      (Classical.choice
        (T.clauseB.q_comparison ((nativeBadLift T).lift b)
          (by
            rw [(nativeBadLift T).lift_comap b]
            exact b.2))).parameter := rfl

/-! ### 5. Rows -/

def tateUniformizerRows : List (String × String) :=
  [ ("order-1 FinitePlaceQCandidate from an actual uniformizer (any K, place)", "PROVED"),
    ("SourceTateComparisonWitness with uniformizer parameter", "CONSTRUCTED (given TateCurveComparison)"),
    ("clause B from uniformizer comparisons", "CONSTRUCTED (conditional)"),
    ("qVFamily order = 1 from constructed clause B", "NOT TRANSPORTABLE (Classical.choice opaque)"),
    ("correct usage: TateUniformizerCondition on actual qVFamily", "PROVED (Mzk1QOrderOneActual)"),
    ("TateCurveComparison realization", "GAP (no constructor; S2806RealizationGap)"),
    ("vendor TateCurvesTheta normalized order (orderZ, localHeight)", "GREEN (78/78 vendor)") ]

theorem tateUniformizerRows_length : tateUniformizerRows.length = 7 := rfl

#check uniformizerCandidate_order
#check uniformizerWitness_order
#check clauseB_of_uniformizerComparisons
#check tateUniformizerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TateUniformizerConstructionActual
end
