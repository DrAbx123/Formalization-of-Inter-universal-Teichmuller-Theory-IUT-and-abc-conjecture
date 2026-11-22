import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic

/-!
# D4 reduction pass, second increment: Tate identification and the 2l-th root

Source: IUT I, Definition 3.1(b) (the elements of V(F) lying over the bad
moduli set Vbad_mod have bad, i.e. multiplicative, reduction; corpus text
lines 3142-3147), Definition 3.1(c) (l is prime to the residue
characteristics of the elements of Vbad_mod and to the orders of the
q-parameters, corpus lines 3180-3184), Definition 3.1(e) (the restriction
section V -> V_mod of V(K) -> V_mod, corpus lines 3216-3220), and
Example 3.2(iv) (q_v lies in the structural sheaf O^{tri}(T_x); q_v has a
2l-th root; the root q_v^{1/2l} is determined only up to a mu_{2l}(T_x)
multiple; corpus lines 3701-3726).

The second increment of the D4 slot has two card-level parts, kept
separate from the first increment (`SourcePlacePartitionReduction.lean`):

* (a) `BadPlaceTateUniformizationCards`: the frozen per-place card bundling a
  completion q-parameter candidate, a Tate curve comparison realizing the
  base-changed curve, and prime-to-l coprimality of the parameter order,
  quantified over every finite place of F lying over Vbad_mod.  The derived
  curve-indexed uniformization, the Clause (b) witness bridge, and the
  assembly of `SourceClauseB` from the card are constructed here.  The card
  itself is conditional: an instance of it is precisely the missing
  elliptic-Tate content, and none is asserted.

* (b) `QParameterTwoLRootCard`: the frozen card for a 2l-th root of a
  q-parameter candidate in the completion, together with the proved
  mu_{2l} indeterminacy law (the ratio of any two 2l-th roots of a nonzero
  element is a 2l-th root of unity) and the proved existence of a 2l-th root
  in the algebraic closure of the completion, as a unit and as an element.
  The descent of the root to the completion (Kummer surjectivity) and the
  membership in the orbifold structural sheaf O^{tri}(T_x) of the paper
  remain open and are registered as pending obligations in the audit block.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

noncomputable section

universe u

namespace InitialThetaSource

namespace PlaceQParameterUniformization

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-! ## (a) the bad-place Tate-uniformization identification card -/

/-- The frozen D4 identification card: for every finite place of `F` whose
restriction to `Fmod` lies in the bad moduli set `V_mod_bad`, a q-parameter
candidate on the completion, a Tate curve comparison realizing the
base-changed curve at that place, and prime-to-l coprimality of the parameter
order.  Source: IUT I, Definition 3.1(b) (elements of V(F) lying over
Vbad_mod have multiplicative reduction) together with (c) and (e). -/
structure BadPlaceTateUniformizationCards (P : SourcePlaceSelection A) where
  parameter : ∀ (w : NumberField.FinitePlace A.F),
    NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad →
      NumberFieldFinitePlace.FinitePlaceQCandidate w
  comparison : ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      TateCurveComparison A.curve w (parameter w hw)
  order_coprime : ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime (parameter w hw).order l.value

namespace BadPlaceTateUniformizationCards

variable {P : SourcePlaceSelection A}

/-- The curve-indexed Tate uniformization derived from the card comparison. -/
def uniformization (C : BadPlaceTateUniformizationCards P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    CurveIndexedTateUniformization A.curve w (C.parameter w hw) :=
  (C.comparison w hw).toUniformization

theorem uniformization_realizesCurve (C : BadPlaceTateUniformizationCards P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    (C.uniformization w hw).coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion w) (C.parameter w hw).q =
      (A.curve.baseChange (NumberFieldFinitePlace.Completion w)).curve :=
  CurveIndexedTateUniformization.coordinate_realization (C.uniformization w hw)

/-- The point comparison underlying the card. -/
def pointComparison (C : BadPlaceTateUniformizationCards P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    TatePointComparison A.curve w (C.parameter w hw) :=
  (C.comparison w hw).points

/-- The card yields the exact Clause (b) comparison witness. -/
def witness (C : BadPlaceTateUniformizationCards P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    SourceTateComparisonWitness A w :=
  SourceTateComparisonWitness.ofComparison (C.parameter w hw)
    (C.comparison w hw) (C.order_coprime w hw)

theorem witness_nonempty (C : BadPlaceTateUniformizationCards P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    Nonempty (SourceTateComparisonWitness A w) :=
  ⟨C.witness w hw⟩

end BadPlaceTateUniformizationCards

variable {S : SourceSignQuotientData A}
variable {CA : SourceClauseA A S}

/-- Clause (b) assembly: given the identification of the sign-quotient bad
moduli set with the place-selection bad set, the multiplicative-reduction
function, the frozen uniformization card, and residue-characteristic
coprimality, the source clause (b) record is assembled.  No instance of the
card is constructed. -/
theorem sourceClauseB_of_tateUniformizationCards
    (P : SourcePlaceSelection A)
    (hV_mod_bad : S.V_mod_bad = P.V_mod_bad)
    (multiplicative : ∀ w : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ S.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt w)
    (C : BadPlaceTateUniformizationCards P)
    (residueCoprime : ∀ w : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ S.V_mod_bad →
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) w))) :
    SourceClauseB A S CA :=
  SourceClauseB.ofTateComparisonWitnesses multiplicative
    (fun w hw => ⟨C.witness w (hV_mod_bad ▸ hw)⟩) residueCoprime

/-- Clause (b) assembly from the two frozen card families of the first
increment (`PlacePartitionReduction.BadPlaceReductionCards` and
`PlacePartitionReduction.BadPlaceQParameterCards`) together with the
uniformization card. -/
theorem sourceClauseB_of_reductionAndQParameterCards
    (P : SourcePlaceSelection A)
    (hV_mod_bad : S.V_mod_bad = P.V_mod_bad)
    (reduction : PlacePartitionReduction.BadPlaceReductionCards P)
    (qParameter : PlacePartitionReduction.BadPlaceQParameterCards P)
    (C : BadPlaceTateUniformizationCards P) :
    SourceClauseB A S CA :=
  sourceClauseB_of_tateUniformizationCards P hV_mod_bad
    (fun w hw => reduction.multiplicativeReduction w (hV_mod_bad ▸ hw))
    C
    (fun w hw =>
      (qParameter.badResidueCharacteristic_primeToL
        (NumberFieldFinitePlace.comap (k := A.Fmod) w)
        (hV_mod_bad ▸ hw)).symm)

/-! ## (b) the 2l-th root of the q-parameter and mu_{2l} indeterminacy -/

/-- `2 * l` is positive for every source prime `l >= 5`. -/
theorem twoL_pos (l : PrimeGeFive) : 0 < 2 * l.value :=
  Nat.mul_pos (by norm_num) l.prime.pos

theorem twoL_ne_zero (l : PrimeGeFive) : 2 * l.value ≠ 0 :=
  (twoL_pos l).ne'

/-- Two 2l-th roots of a nonzero element differ by a 2l-th root of unity. -/
theorem twoLRoot_ratio_pow_eq_one {K : Type u} [Field K] {q : K} (hq : q ≠ 0)
    {r₁ r₂ : K} (h₁ : r₁ ^ (2 * l.value) = q) (h₂ : r₂ ^ (2 * l.value) = q) :
    (r₁ / r₂) ^ (2 * l.value) = 1 := by
  rw [div_pow, h₁, h₂, div_self hq]

/-- The ratio of two 2l-th roots of a unit lies in mu_{2l}. -/
theorem twoLRootUnit_ratio_mem_rootsOfUnity {K : Type u} [Field K] {qUnit : Kˣ}
    {r₁ r₂ : Kˣ} (h₁ : r₁ ^ (2 * l.value) = qUnit)
    (h₂ : r₂ ^ (2 * l.value) = qUnit) :
    r₁ / r₂ ∈ rootsOfUnity (2 * l.value) K := by
  rw [mem_rootsOfUnity]
  rw [div_pow, h₁, h₂]
  exact div_self' qUnit

/-- The frozen reduction-pass card for the object "q^{1/2l}" of Example
3.2(iv): a nonzero 2l-th root of the q-parameter candidate inside the
completion.  An instance of this card is genuine Kummer-type input (the
2l-th power map is not known to be surjective on the completion); it is not
constructed from the arithmetic data here. -/
structure QParameterTwoLRootCard
    (l : PrimeGeFive) {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) where
  root : NumberFieldFinitePlace.Completion place
  root_ne_zero : root ≠ 0
  root_pow : root ^ (2 * l.value) = parameter.q

namespace QParameterTwoLRootCard

variable {K : Type u} [Field K] [NumberField K]
variable {l : PrimeGeFive} {place : NumberField.FinitePlace K}
variable {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}

/-- Named constructor for the 2l-th-root card. -/
def ofRoot (root : NumberFieldFinitePlace.Completion place) (root_ne_zero : root ≠ 0)
    (root_pow : root ^ (2 * l.value) = parameter.q) :
    QParameterTwoLRootCard l place parameter where
  root := root
  root_ne_zero := root_ne_zero
  root_pow := root_pow

/-- A 2l-th root of the q-parameter candidate has valuation below one. -/
theorem root_valuation_lt_one (card : QParameterTwoLRootCard l place parameter) :
    (Valued.v card.root : WithZero (Multiplicative Int)) < 1 := by
  by_contra h
  have hge : (1 : WithZero (Multiplicative Int)) ≤
      (Valued.v card.root : WithZero (Multiplicative Int)) :=
    le_of_not_gt h
  have hpow : (1 : WithZero (Multiplicative Int)) ≤
      (Valued.v card.root : WithZero (Multiplicative Int)) ^ (2 * l.value) :=
    one_le_pow₀ hge
  have hq := parameter.valuation_lt_one
  rw [← card.root_pow] at hq
  rw [map_pow] at hq
  exact not_lt_of_ge hpow hq

/-- The 2l-th root is again a valuation-theoretic q-candidate. -/
def toQCandidate (card : QParameterTwoLRootCard l place parameter) :
    NumberFieldFinitePlace.FinitePlaceQCandidate place where
  q := card.root
  q_ne_zero := card.root_ne_zero
  valuation_lt_one := card.root_valuation_lt_one

@[simp] theorem toQCandidate_q (card : QParameterTwoLRootCard l place parameter) :
    card.toQCandidate.q = card.root := rfl

theorem toQCandidate_valuation_lt_one
    (card : QParameterTwoLRootCard l place parameter) :
    (Valued.v card.toQCandidate.q : WithZero (Multiplicative Int)) < 1 :=
  card.toQCandidate.valuation_lt_one

/-- Any other 2l-th root of the parameter differs from the card root by a
2l-th root of unity. -/
theorem ratio_pow_eq_one (card : QParameterTwoLRootCard l place parameter)
    {r : NumberFieldFinitePlace.Completion place}
    (hr : r ^ (2 * l.value) = parameter.q) :
    (r / card.root) ^ (2 * l.value) = 1 :=
  twoLRoot_ratio_pow_eq_one (l := l) (q := parameter.q) parameter.q_ne_zero hr
    card.root_pow

end QParameterTwoLRootCard

/-- In the completion, any two 2l-th roots of the q-parameter candidate
differ by a mu_{2l}-element. -/
theorem qParameterTwoLRoot_ratio_pow_eq_one {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K}
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place)
    {r₁ r₂ : NumberFieldFinitePlace.Completion place}
    (h₁ : r₁ ^ (2 * l.value) = parameter.q)
    (h₂ : r₂ ^ (2 * l.value) = parameter.q) :
    (r₁ / r₂) ^ (2 * l.value) = 1 :=
  twoLRoot_ratio_pow_eq_one (l := l) (q := parameter.q) parameter.q_ne_zero h₁ h₂

/-- Unit form of the mu_{2l} indeterminacy of q^{1/2l} in the completion. -/
theorem qParameterTwoLRootUnit_ratio_mem_rootsOfUnity {K : Type u} [Field K]
    [NumberField K] {place : NumberField.FinitePlace K}
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place)
    {r₁ r₂ : (NumberFieldFinitePlace.Completion place)ˣ}
    (h₁ : r₁ ^ (2 * l.value) = Units.mk0 parameter.q parameter.q_ne_zero)
    (h₂ : r₂ ^ (2 * l.value) = Units.mk0 parameter.q parameter.q_ne_zero) :
    r₁ / r₂ ∈ rootsOfUnity (2 * l.value)
      (NumberFieldFinitePlace.Completion place) :=
  twoLRootUnit_ratio_mem_rootsOfUnity (l := l)
    (qUnit := Units.mk0 parameter.q parameter.q_ne_zero) h₁ h₂

/-- Route 2 of the root extraction (root tower inside the algebraic
closure): q has a 2l-th root in the units of the algebraic closure of the
completion. -/
theorem exists_twoLRoot_unit_in_algebraicClosure {K : Type u} [Field K]
    [NumberField K] {place : NumberField.FinitePlace K}
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) :
    ∃ r : (AlgebraicClosure (NumberFieldFinitePlace.Completion place))ˣ,
      r ^ (2 * l.value) =
        NumberFieldFinitePlace.tateParameterUnit place parameter.q
          parameter.q_ne_zero :=
  AlgebraicClosureRootSystem.exists_pow_root
    (NumberFieldFinitePlace.tateParameterUnit place parameter.q parameter.q_ne_zero)
    (2 * l.value) (twoL_ne_zero l)

/-- Element form of the algebraic-closure root extraction. -/
theorem exists_twoLRoot_element_in_algebraicClosure {K : Type u} [Field K]
    [NumberField K] {place : NumberField.FinitePlace K}
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) :
    ∃ z : AlgebraicClosure (NumberFieldFinitePlace.Completion place),
      z ^ (2 * l.value) =
        algebraMap (NumberFieldFinitePlace.Completion place)
          (AlgebraicClosure (NumberFieldFinitePlace.Completion place))
          parameter.q := by
  obtain ⟨r, hr⟩ := exists_twoLRoot_unit_in_algebraicClosure (l := l) parameter
  refine ⟨(r : AlgebraicClosure (NumberFieldFinitePlace.Completion place)), ?_⟩
  have hval := congrArg
    (fun u : (AlgebraicClosure (NumberFieldFinitePlace.Completion place))ˣ =>
      (u : AlgebraicClosure (NumberFieldFinitePlace.Completion place))) hr
  simpa [NumberFieldFinitePlace.tateParameterUnit, Units.val_pow_eq_pow_val,
    Units.coe_map, Units.val_mk0] using hval

end PlaceQParameterUniformization

end InitialThetaSource

namespace Audit

/-- The D4 Tate-identification increment: the card is frozen and the
Clause (b) assembly is constructed; producing an instance of the card is the
pending content. -/
def placeTateUniformizationIdentification : Obligation :=
  { id := "IUT-I.definition-3.1-D4-tate-uniformization-identification"
    source :=
      "IUT I, Definition 3.1(b) with (c)(e): the q-parameter and the " ++
        "Tate identification over Vbad_mod"
    status := VerificationStatus.conditional
    note :=
      "Frozen: for every finite place of F lying over the bad moduli set, a " ++
        "completion q-parameter candidate, a Tate curve comparison realizing " ++
        "the base-changed curve, and prime-to-l coprimality of its order. " ++
        "Constructed from the card: the curve-indexed uniformization, the " ++
        "point comparison, the Clause (b) witness, and the assembly of " ++
        "SourceClauseB (also from the first-increment reduction and " ++
        "q-parameter cards). Producing an instance of the card is exactly " ++
        "the pending elliptic-Tate content; no instance is asserted."
    dependsOn :=
      [ "IUT-I.definition-3.1-D4-reduction-cards",
        "IUT-I.definition-3.1-A2-clause-constructors",
        "Foundations.Geometry.elliptic-tate-uniformization",
        "Foundations.Geometry.tate-point-quotient-boundary",
        "Foundations.Geometry.curve-indexed-tate-uniformization" ] }

/-- The proved kernel of the 2l-th root extraction and mu_{2l}
indeterminacy. -/
def qParameterTwoLRootExtraction : Obligation :=
  { id := "IUT-I.definition-3.1-D4-q-2l-root-extraction"
    source :=
      "IUT I, Example 3.2(iv): the 2l-th root of the q-parameter, " ++
        "determined up to a mu_{2l}-multiple"
    status := VerificationStatus.provedKernel
    note :=
      "Proved: 2*l is positive; the ratio of any two 2l-th roots of a " ++
        "nonzero element is a 2l-th root of unity (the mu_{2l} " ++
        "indeterminacy law), in element and unit forms; a 2l-th root of the " ++
        "q-parameter candidate always exists in the algebraic closure of " ++
        "the completion, as a unit and as an element; and the 2l-th root is " ++
        "again a q-candidate of valuation below one. Not proved: descent of " ++
        "the root to the completion itself, and membership in the orbifold " ++
        "structural sheaf of the paper."
    dependsOn :=
      [ "IUT-I.definition-3.1-D4-reduction-cards",
        "IUT-II.natural-compatible-root-system",
        "Foundations.NumberField.local-q-parameter-valuation" ] }

/-- The parked residue: descent of q^{1/2l} to the completion, and the
orbifold membership of Example 3.2(iv). -/
def qParameterTwoLRootDescent : Obligation :=
  { id := "IUT-I.definition-3.1-D4-q-2l-root-descent"
    source :=
      "IUT I, Example 3.2(iv): q_v^{1/2l} lies in the structural sheaf, " ++
        "determined up to mu_{2l}"
    status := VerificationStatus.pending
    note :=
      "Open (parked): no formalized Kummer-theoretic surjectivity of the " ++
        "2l-th power map on principal units, no Hensel or Kummer input " ++
        "giving the 2l-th root inside the completion or its integers, and no " ++
        "carrier for the orbifold structural sheaf O^{tri}(T_x) of the " ++
        "paper are available. The algebraic-closure root and the mu_{2l} " ++
        "ratio law are proved in this module; the descent is not."
    dependsOn :=
      [ "IUT-I.definition-3.1-D4-q-2l-root-extraction" ] }

end Audit

end

end LeanFormal.IUT
