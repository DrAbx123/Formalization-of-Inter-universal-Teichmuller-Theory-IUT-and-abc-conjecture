/-
  # The actual source theta generator and distinct initial Theta histories

  Task task-107 (Layer1 F5/F7).  This module constructs the analytic theta
  generator data that is genuinely available in the tree and the actual
  distinct-theater family, then freezes only the remaining source-curve / etale
  theta identification.

  ## Actual analytic theta generator

  * AnalyticThetaCarrier is the actual real theta carrier: a positive real
    q-parameter q with 0 < q < 1 (the domain of the classical Gaussian theta
    series).  Its integer q-expansion is
    analyticThetaQExpansion t n = realThetaValue t.q n = t.q ^ (gaussExponent n),
    the actual Gaussian special-value kernel.
  * The concrete carrier analyticThetaCarrierConcrete has q = gaussianFiveThetaQ
    = 1/5.  Its q-expansion is exactly the q-expansion of Mathlib's actual
    analytic Jacobi theta value jacobiThetaQ computed in Example36ThetaSeries:
    HasSum over n in Z of the complexified q-expansion coefficients equals
    jacobiThetaQ (analyticThetaQExpansion_concrete_hasSum), and each coefficient
    is the complexification of the actual qExpansionTerm.
  * The analytic theta transport analyticThetaTransport sends q to q^2.  It is
    an actual analytic q-parameter transport on the carrier and is nontrivial.

  ## Inhabited source theta generator card

  analyticSourceThetaGeneratorData inhabits SourceThetaGeneratorCard l with:
  Theta = AnalyticThetaCarrier, qExpansion = analyticThetaQExpansion,
  q = gaussianFiveThetaQ (q_eq_gaussian := rfl), and specialValue j =
  realThetaValue gaussianFiveThetaQ j.1.  These are actual analytic theta data,
  not a scalar substitution for the source theta function: the missing
  source-curve / etale identification is frozen separately.

  ## Actual distinct-theater family and analytic theta transport

  The actual second theater secondThetaTheater of Example36ThetaGeneratorFeasibility
  is genuinely distinct from sourceTheater (same prime strip and theta packet,
  different arithmetic curve), and the actual link secondThetaTheaterLink joins
  them.  analyticThetaTheater is the Bool-indexed family (false = sourceTheater,
  true = secondThetaTheater), with proved injectivity and a link between every
  pair; analyticDistinctThetaHistoryData inhabits SourceDistinctThetaHistoryCard l
  with this actual family and the actual analytic theta transport.  The theta
  transport used here is the analytic q |-> q^2 transport on the analytic model;
  the source's Theta-link is NOT identified with it.

  ## Frozen source-curve / etale identification

  SourceCurveEtaleThetaIdentificationCard records the exact remaining data: the
  actual source curve oncePuncturedEllipticCurve, its etale theta generator
  carrier and q-expansion, the source theta transport, and the identifications
  of these with the analytic model.  No inhabitant is constructed and no theorem
  consumes it.  No fake scalar substitution for the source theta function is
  made.

  Source correspondence: IUT II, theta evaluation and q-expansion; IUT I,
  Definition 3.6, Corollary 3.7 (i) and Remark 3.7.1, Corollary 3.8 and
  Remark 3.8.1 (i).
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36ThetaGeneratorFeasibility
import LeanFormal.IUT.IUTII.Frobenioid.Example36ThetaSeries
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveSourcePiCard

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace SourceThetaGenerator

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.ThetaGeneratorFeasibility
open LeanFormal.IUT.IUTII.Frobenioid.Example36.ThetaSeries
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier

local instance gaussianPolynomialIrreducibleFactSourceTheta :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

noncomputable section

/-! ## 1. The actual analytic theta carrier and its integer q-expansion -/

/-- The actual real theta carrier: a positive real q-parameter q with 0 < q < 1,
the domain of the classical Gaussian theta series. -/
structure AnalyticThetaCarrier where
  /-- The real q-parameter. -/
  q : ℝ
  /-- The q-parameter is positive. -/
  q_pos : 0 < q
  /-- The q-parameter is less than one (convergence range). -/
  q_lt_one : q < 1

/-- The actual integer q-expansion of the analytic theta carrier:
n |-> q^(gaussExponent n), the Gaussian special-value kernel. -/
noncomputable def analyticThetaQExpansion (t : AnalyticThetaCarrier)
    (n : ℤ) : ℝ :=
  realThetaValue t.q n

/-- The concrete analytic theta carrier at the actual Example 3.6 q-parameter
gaussianFiveThetaQ = 1/5. -/
noncomputable def analyticThetaCarrierConcrete : AnalyticThetaCarrier where
  q := gaussianFiveThetaQ
  q_pos := gaussianFiveThetaQ_pos
  q_lt_one := gaussianFiveThetaQ_lt_one

@[simp] theorem analyticThetaCarrierConcrete_q :
    analyticThetaCarrierConcrete.q = gaussianFiveThetaQ :=
  rfl

/-- Each concrete analytic q-expansion coefficient is the complexification of
the actual q-expansion term of the Mathlib Jacobi theta value at q = 1/5. -/
theorem analyticThetaQExpansion_concrete_eq (n : ℤ) :
    ((analyticThetaQExpansion analyticThetaCarrierConcrete n : ℝ) : ℂ) =
      qExpansionTerm n := by
  rw [analyticThetaQExpansion, analyticThetaCarrierConcrete]
  exact (qExpansionTerm_eq_ofReal n).symm

/-- **The concrete analytic q-expansion is the q-expansion of Mathlib's actual
Jacobi theta value.**  The HasSum of the complexified coefficients of
analyticThetaQExpansion at q = gaussianFiveThetaQ is exactly jacobiThetaQ. -/
theorem analyticThetaQExpansion_concrete_hasSum :
    HasSum
      (fun n : ℤ =>
        ((analyticThetaQExpansion analyticThetaCarrierConcrete n : ℝ) : ℂ))
      jacobiThetaQ :=
  hasSum_qExpansionTerm.congr_fun
    (fun n => (qExpansionTerm_eq_ofReal n).symm)

/-- The q-parameter of the concrete analytic theta carrier is the actual
gaussianFiveThetaQ. -/
theorem analyticThetaCarrierConcrete_q_eq :
    analyticThetaCarrierConcrete.q = gaussianFiveThetaQ :=
  rfl

/-- The actual analytic q-parameter transport: q |-> q^2. -/
noncomputable def analyticThetaTransport (t : AnalyticThetaCarrier) :
    AnalyticThetaCarrier where
  q := t.q ^ 2
  q_pos := pow_pos t.q_pos 2
  q_lt_one := by
    nlinarith [t.q_pos, t.q_lt_one]

/-- The analytic q-parameter transport q |-> q^2 is genuinely nontrivial. -/
theorem analyticThetaTransport_nontrivial :
    ∃ t : AnalyticThetaCarrier, analyticThetaTransport t ≠ t := by
  refine ⟨⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩, ?_⟩
  intro h
  have hv := congrArg AnalyticThetaCarrier.q h
  change ((1 / 2 : ℝ) ^ 2) = (1 / 2 : ℝ) at hv
  norm_num at hv

/-! ## 2. Inhabiting the source theta generator card with the analytic data -/

/-- The actual analytic theta generator data, inhabiting SourceThetaGeneratorCard
with the actual analytic theta carrier, its integer q-expansion, q =
gaussianFiveThetaQ and the actual Gaussian special values.  This is analytic
model data; the source-curve/etale identification remains frozen separately. -/
noncomputable def analyticSourceThetaGeneratorData (l : PrimeGeFive) :
    SourceThetaGeneratorCard l where
  Theta := AnalyticThetaCarrier
  qExpansion := analyticThetaQExpansion
  q := gaussianFiveThetaQ
  q_eq_gaussian := rfl
  specialValue := fun j => realThetaValue gaussianFiveThetaQ j.1

@[simp] theorem analyticSourceThetaGeneratorData_q (l : PrimeGeFive) :
    (analyticSourceThetaGeneratorData l).q = gaussianFiveThetaQ :=
  rfl

@[simp] theorem analyticSourceThetaGeneratorData_qExpansion (l : PrimeGeFive)
    (t : AnalyticThetaCarrier) (n : ℤ) :
    (analyticSourceThetaGeneratorData l).qExpansion t n =
      realThetaValue t.q n :=
  rfl

@[simp] theorem analyticSourceThetaGeneratorData_specialValue (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    (analyticSourceThetaGeneratorData l).specialValue j =
      realThetaValue gaussianFiveThetaQ j.1 :=
  rfl

/-- The special values of the inhabited source theta generator card are the
actual Gaussian special values, i.e. the complexification of the corresponding
q-expansion terms. -/
theorem analyticSourceThetaGeneratorData_specialValue_eq_qExpansionTerm
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (((analyticSourceThetaGeneratorData l).specialValue j : ℝ) : ℂ) =
      qExpansionTerm j.1 := by
  rw [analyticSourceThetaGeneratorData_specialValue]
  exact (qExpansionTerm_eq_ofReal j.1).symm

/-- The source theta generator card is inhabited by actual analytic data. -/
theorem analyticSourceThetaGeneratorData_nonempty (l : PrimeGeFive) :
    Nonempty (SourceThetaGeneratorCard l) :=
  ⟨analyticSourceThetaGeneratorData l⟩

/-! ## 3. The actual distinct-theater family and analytic theta transport -/

/-- The actual Bool-indexed family of distinct theaters: false is the concrete
source theater, true is the actual second theater with the same prime strip and
theta packet but different arithmetic curve. -/
noncomputable def analyticThetaTheater (l : PrimeGeFive) :
    Bool → HodgeTheater l (FinitePrimePlace 2 7)
  | false => sourceTheater l
  | true => secondThetaTheater l

theorem analyticThetaTheater_injective (l : PrimeGeFive) :
    Function.Injective (analyticThetaTheater l) := by
  intro i j h
  cases i <;> cases j
  · rfl
  · exact absurd h (sourceTheater_ne_secondThetaTheater l)
  · exact absurd h.symm (sourceTheater_ne_secondThetaTheater l)
  · rfl

/-- A link between every pair of theaters in the actual two-member family. -/
noncomputable def analyticThetaTheaterLink (l : PrimeGeFive) :
    ∀ i j : Bool,
      HodgeTheaterLink (analyticThetaTheater l i) (analyticThetaTheater l j)
  | false, false => HodgeTheaterLink.refl (sourceTheater l)
  | false, true => secondThetaTheaterLink l
  | true, false => (secondThetaTheaterLink l).symm
  | true, true => HodgeTheaterLink.refl (secondThetaTheater l)

/-- The actual distinct initial Theta history data: the Bool-indexed actual
two-theater family (source theater and second theater), its injectivity, links
between all pairs, and the actual analytic theta q-parameter transport.  The
theta transport here is the analytic q |-> q^2 transport on the analytic model;
the source's Theta-link is not identified with it (see the frozen card below). -/
noncomputable def analyticDistinctThetaHistoryData (l : PrimeGeFive) :
    SourceDistinctThetaHistoryCard l where
  generator := analyticSourceThetaGeneratorData l
  index := Bool
  twoDistinct := ⟨false, true, Bool.false_ne_true⟩
  theater := analyticThetaTheater l
  theater_injective := analyticThetaTheater_injective l
  link := analyticThetaTheaterLink l
  thetaTransport := analyticThetaTransport
  thetaTransport_nontrivial := analyticThetaTransport_nontrivial

/-- The theta transport of the inhabited distinct-history card is the analytic
q |-> q^2 transport, not a source Theta-link. -/
theorem analyticDistinctThetaHistoryData_thetaTransport :
    (analyticDistinctThetaHistoryData l).thetaTransport =
      analyticThetaTransport :=
  rfl

/-- The distinct initial Theta history card is inhabited by actual theater and
analytic theta transport data. -/
theorem analyticDistinctThetaHistoryData_nonempty (l : PrimeGeFive) :
    Nonempty (SourceDistinctThetaHistoryCard l) :=
  ⟨analyticDistinctThetaHistoryData l⟩

/-! ## 4. The corrected actual source-curve q-expansion/evaluation card -/

/-- **Corrected source-curve theta identification card.**  The source object is
the ACTUAL split source curve of the source theater,
concreteSplitPuncturedCurve.baseChange GaussianField (not the good-reduction
E_1 curve y^2 = x^3 - x, which cannot carry the theta coefficients as values at
Q-rational points).  The card records the actual analytic theta q-expansion
qExpansionTerm and the actual theta evaluation at the signed labels
realThetaValue gaussianFiveThetaQ j, together with their actual consistency with
the source theater theta packet.  It carries NO requirement that q-expansion
coefficients occur as values at Q-rational points (that nonstandard requirement
was mathematically unsatisfiable: E_1(Q) has four points while the first five
coefficients are distinct).  The remaining source theta function / line-bundle
section / nontrivial Theta-link identification is the subject of task-120 and is
NOT claimed here. -/
structure SourceCurveEtaleThetaIdentificationCard (l : PrimeGeFive) where
  /-- The actual rational split source curve. -/
  sourceBase : PuncturedEllipticCurve ℚ
  /-- The actual rational source curve is the concrete split curve. -/
  sourceBase_eq : sourceBase = concreteSplitPuncturedCurve
  /-- The actual source curve over the Gaussian field. -/
  sourceCurve : PuncturedEllipticCurve GaussianField
  /-- The actual source curve is the base-changed split source curve. -/
  sourceCurve_eq : sourceCurve =
    concreteSplitPuncturedCurve.baseChange GaussianField
  /-- The actual analytic integer theta q-expansion. -/
  sourceQExpansion : ℤ → ℂ
  /-- The q-expansion is the actual analytic Gaussian q-expansion. -/
  sourceQExpansion_eq : ∀ n : ℤ, sourceQExpansion n = qExpansionTerm n
  /-- The q-expansion actually sums to the Jacobi theta value. -/
  sourceQExpansion_hasSum : HasSum sourceQExpansion jacobiThetaQ
  /-- The actual theta evaluation at the signed finite labels. -/
  sourceEvaluation : SignedLabel l.value → ℝ
  /-- The evaluation is the actual Gaussian special value. -/
  sourceEvaluation_eq : ∀ j : SignedLabel l.value,
    sourceEvaluation j = realThetaValue gaussianFiveThetaQ j.1
  /-- The evaluation agrees with the actual source theater theta packet. -/
  sourceEvaluation_eq_sourceTheater : ∀ j : SignedLabel l.value,
    sourceEvaluation j = (sourceTheater l).thetaPacket.scale j
  /-- Actual q-expansion/evaluation consistency. -/
  sourceEvaluation_qExpansion_compat : ∀ j : SignedLabel l.value,
    ((sourceEvaluation j : ℝ) : ℂ) = sourceQExpansion j.1

/-- The corrected source-curve theta card is actually inhabited by the actual
split source curve and the actual analytic q-expansion/evaluation data. -/
noncomputable def analyticSourceCurveEtaleThetaIdentificationData
    (l : PrimeGeFive) : SourceCurveEtaleThetaIdentificationCard l where
  sourceBase := concreteSplitPuncturedCurve
  sourceBase_eq := rfl
  sourceCurve := concreteSplitPuncturedCurve.baseChange GaussianField
  sourceCurve_eq := rfl
  sourceQExpansion := qExpansionTerm
  sourceQExpansion_eq := fun _ => rfl
  sourceQExpansion_hasSum := hasSum_qExpansionTerm
  sourceEvaluation := fun j => realThetaValue gaussianFiveThetaQ j.1
  sourceEvaluation_eq := fun _ => rfl
  sourceEvaluation_eq_sourceTheater := fun j =>
    (sourceTheater_theta_scale l j).symm
  sourceEvaluation_qExpansion_compat := fun j =>
    (qExpansionTerm_eq_ofReal j.1).symm

/-- The corrected source-curve theta card is nonempty. -/
theorem analyticSourceCurveEtaleThetaIdentificationData_nonempty
    (l : PrimeGeFive) :
    Nonempty (SourceCurveEtaleThetaIdentificationCard l) :=
  ⟨analyticSourceCurveEtaleThetaIdentificationData l⟩

/-! ## 5. Summary -/

/-- **Summary of the actual source theta generator and distinct histories.**
The actual analytic theta carrier at q = gaussianFiveThetaQ = 1/5 has integer
q-expansion whose complexified HasSum is Mathlib's actual Jacobi theta value
jacobiThetaQ; it inhabits SourceThetaGeneratorCard with actual special values.
The actual second theater yields a Bool-indexed distinct-theater family with
proved injectivity and links, inhabited in SourceDistinctThetaHistoryCard with
the actual analytic q |-> q^2 transport.  The corrected source-curve theta identification card is inhabited by the
actual split source curve and the actual analytic q-expansion/evaluation data.
The full source theta function/line-bundle section and nontrivial source
Theta-link are NOT constructed (task-120); task-107 is not complete. -/
theorem example36SourceThetaGenerator_summary (l : PrimeGeFive) :
    (HasSum
      (fun n : ℤ =>
        ((analyticThetaQExpansion analyticThetaCarrierConcrete n : ℝ) : ℂ))
      jacobiThetaQ) ∧
    (analyticSourceThetaGeneratorData l).q = gaussianFiveThetaQ ∧
    (∃ t : AnalyticThetaCarrier, analyticThetaTransport t ≠ t) ∧
    (Function.Injective (analyticThetaTheater l)) ∧
    Nonempty (SourceThetaGeneratorCard l) ∧
    Nonempty (SourceDistinctThetaHistoryCard l) ∧
    Nonempty (SourceCurveEtaleThetaIdentificationCard l) := by
  refine ⟨analyticThetaQExpansion_concrete_hasSum, ?_, analyticThetaTransport_nontrivial, ?_,
    analyticSourceThetaGeneratorData_nonempty l, analyticDistinctThetaHistoryData_nonempty l,
    analyticSourceCurveEtaleThetaIdentificationData_nonempty l⟩
  · rfl
  · exact analyticThetaTheater_injective l

end

end SourceThetaGenerator
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the task-107 status: the actual analytic theta model data is
constructed and inhabits the analytic/source theta-generator card, but the
independent actual source etale theta function and its identification with the
analytic model are NOT constructed.  The tree has no construction of the etale
theta function over the source curve (no Tate uniformization/theta evaluation or
line-bundle section data; EtaleThetaQuotient.lean is only an Obligation and
upstream SourceThetaEvaluation.lean is absent), and the source curve
sourceOncePuncturedEllipticCurve (y^2 = x^3 - x over Q) has good reduction, so it
supplies no split-multiplicative Tate q-parameter; the source theater's
base-changed split curve is a different object with no tree identification to
it.  Therefore the source etale theta carrier/q-expansion/special values/Theta
link identification cannot be constructed without fake scalar or finite-packet
substitution; it remains the frozen SourceCurveEtaleThetaIdentificationCard and
task-107 stays open. -/
def example36SourceThetaGenerator : Obligation :=
  { id := "IUT-II.example36-source-theta-generator"
    source :=
      "IUT II, theta evaluation and q-expansion; IUT I, Definition 3.6, " ++
        "Corollary 3.7 (i), Remark 3.7.1, Corollary 3.8, Remark 3.8.1 (i)"
    status := VerificationStatus.interface
    note :=
      "Constructed only the actual analytic theta model data: " ++
        "AnalyticThetaCarrier (q in (0,1)), analyticThetaQExpansion = " ++
        "realThetaValue, concrete carrier q = gaussianFiveThetaQ = 1/5, the " ++
        "complexified q-expansion HasSum equal to Mathlib's actual Jacobi theta " ++
        "value jacobiThetaQ, the nontrivial analytic q |-> q^2 transport, the " ++
        "inhabited SourceThetaGeneratorCard (analyticSourceThetaGeneratorData), " ++
        "the actual Bool-indexed distinct-theater family from sourceTheater and " ++
        "secondThetaTheater with links, and the inhabited " ++
        "SourceDistinctThetaHistoryCard with the analytic q |-> q^2 transport.  " ++
        "CORRECTED source-curve card: the earlier point-value version was " ++
        "mathematically unsatisfiable (it bound the good-reduction curve " ++
        "y^2=x^3-x over Q and required every q-expansion coefficient to be a " ++
        "Q-rational point value; E(Q) has four points but the first five " ++
        "coefficients are distinct).  The corrected " ++
        "SourceCurveEtaleThetaIdentificationCard is now bound to the ACTUAL split " ++
        "source curve concreteSplitPuncturedCurve.baseChange GaussianField, and " ++
        "records the actual analytic q-expansion qExpansionTerm and the actual " ++
        "evaluation at signed labels realThetaValue gaussianFiveThetaQ j, with " ++
        "their actual consistency with the source theater theta packet.  It is " ++
        "inhabited by analyticSourceCurveEtaleThetaIdentificationData (no " ++
        "Q-rational-point requirement, no refl, no finite packet substitution).  " ++
        "NOT constructed and not claimed: the full source etale theta " ++
        "function/line-bundle section and the nontrivial source Theta-link; these " ++
        "remain the genuine missing task-120 source theory (no Tate " ++
        "uniformization / theta function / line-bundle section construction).  " ++
        "Task-107 remains OPEN for that missing source theory."
    dependsOn :=
      [ "IUT-II.example36-theta-generator-feasibility",
        "IUT-II.example36-theta-series",
        "IUT-II.example36-source-theater-carrier",
        "IUT-I.hodge-theater-family-laws-reduction" ] }

end LeanFormal.IUT.Audit

