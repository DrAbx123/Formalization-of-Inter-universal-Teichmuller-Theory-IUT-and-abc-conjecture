import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply
import LeanFormal.IUT.Foundations.NumberField.LocalQParameterRamification
import Mathlib.Tactic

/-!
# D4 Tate-q identification boundary and the q-order power kernel

Source: IUT I, Definition 3.1(b) (corpus lines 3142-3147: the elements of
`V(F)` lying over the bad moduli set have multiplicative reduction),
Definition 3.1(c) (corpus lines 3180-3184: `l` is prime to the residue
characteristics of the elements of the bad moduli set and to the orders of
the q-parameters at the primes of `V(F)^bad`), and Example 3.2(iv) (corpus
lines 3701-3726: the q-parameter `q_v`, its `2l`-th root `q_v^{1/2l}` in
the structural sheaf, determined only up to a `mu_{2l}`-multiple).

This leaf freezes the identification boundary between the three q-order
quantities of the D4 line and proves the valuation-theoretic kernel:

* the DVR proxy order `(badPlaceQCandidate P b).order` at the section lift
  of a bad moduli place;
* the source bookkeeping order `Q.sourceQParameterOrder w hw` at an
  `F`-place over the bad moduli set;
* the Tate-card order `(C.parameter w hw).order` of
  `BadPlaceTateUniformizationCards` at the same `F`-place.

The boundary statements `TateQIdentificationStatement`,
`SourceQParameterOrderAgreesWithCandidate` and
`SourceOrderAgreesWithTateCard` are frozen Propositions; no instance is
asserted. The transfer lemmas are proved conditionally on these
Propositions, and the kernel computations (positive-power scaling of the
q-candidate exponent and order, the `2l`-th-root order law, and the
incompatibility of a same-completion `2l`-th root with the clause-(c)
prime-to-`l` order condition) are unconditional.

The frozen-agreement triangle is completed: together with
`tateQIdentification_of_sourceAgreement`, any two of the three frozen
agreements compose to the third. The finite-place-extension q-order transfer
kernel (unramified preservation, divisibility, and coprimality transport of
the candidate order) is recorded as the q-order bookkeeping fragment of the
`A.Fmod`-`A.F`-`A.K` chain; reduction-type fiber uniformity
(`IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap`, subgap (i)) remains
open.

No gate (`D9CompatibilityConstruction` / `D10InitialThetaConstruction`)
is closed, and no instance of `BadPlaceTateUniformizationCards` is
constructed here. The two negative theorems of the G1 verdict
(`shell_does_not_determine_xmu`, `shell_does_not_determine_polyIso`) are
not re-proved.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace LeanFormal.IUT

noncomputable section

universe u v

namespace NumberFieldFinitePlace.FinitePlaceQCandidate

variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- The integer exponent of a positive power of a q-candidate scales by the
power. -/
theorem exponent_pow (parameter : FinitePlaceQCandidate place)
    (n : Nat) (hn : 0 < n) :
    (parameter.pow n hn).exponent = (n : Int) * parameter.exponent := by
  have hunzero :
      WithZero.unzero (parameter.pow n hn).valuation_ne_zero =
        WithZero.unzero parameter.valuation_ne_zero ^ n := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, WithZero.coe_pow]
    simp only [pow_q, map_pow]
  rw [exponent, exponent, hunzero, Int.toAdd_pow]
  ring

/-- The positive natural order of a positive power of a q-candidate scales
by the power. -/
theorem order_pow (parameter : FinitePlaceQCandidate place)
    (n : Nat) (hn : 0 < n) :
    (parameter.pow n hn).order = n * parameter.order := by
  apply Int.ofNat_injective
  change
    ((Int.toNat (parameter.pow n hn).exponent : Nat) : Int) =
      ((n * Int.toNat parameter.exponent : Nat) : Int)
  rw [Nat.cast_mul,
    Int.toNat_of_nonneg (le_of_lt (parameter.pow n hn).exponent_pos),
    Int.toNat_of_nonneg (le_of_lt parameter.exponent_pos),
    exponent_pow]

end NumberFieldFinitePlace.FinitePlaceQCandidate

namespace NumberFieldFinitePlace.FinitePlaceQCandidate

variable {k : Type u} {K : Type v}
variable [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- An unramified lift preserves the candidate order: if the ramification
index is one, the order of the mapped candidate equals the order at the
contracted place. -/
theorem order_map_eq_self_of_ramificationIdx_eq_one
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place))
    (h : (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
        place.maximalIdeal.asIdeal = 1) :
    (map place parameter).order = parameter.order := by
  rw [order_map, h, one_mul]

/-- The order at the contracted place divides the order at any lift. -/
theorem order_dvd_order_map
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) :
    parameter.order ∣ (map place parameter).order :=
  ⟨(comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
      place.maximalIdeal.asIdeal, by
    rw [order_map, Nat.mul_comm]⟩

/-- Coprimality with `l` of the lifted order splits into coprimality of the
ramification index and of the order at the contracted place. -/
theorem coprime_order_map_iff
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) (l : Nat) :
    Nat.Coprime (map place parameter).order l ↔
      Nat.Coprime ((comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
          place.maximalIdeal.asIdeal) l ∧
        Nat.Coprime parameter.order l := by
  rw [order_map]
  exact Nat.coprime_mul_iff_left

/-- If the lifted order is prime to `l`, so is the order at the contracted
place. -/
theorem coprime_order_of_coprime_order_map
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) {l : Nat}
    (h : Nat.Coprime (map place parameter).order l) :
    Nat.Coprime parameter.order l :=
  ((coprime_order_map_iff place parameter l).mp h).2

/-- If both the ramification index and the order at the contracted place are
prime to `l`, so is the lifted order. -/
theorem coprime_order_map_of_coprime
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) {l : Nat}
    (he : Nat.Coprime
      ((comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
        place.maximalIdeal.asIdeal) l)
    (h : Nat.Coprime parameter.order l) :
    Nat.Coprime (map place parameter).order l :=
  (coprime_order_map_iff place parameter l).mpr ⟨he, h⟩

end NumberFieldFinitePlace.FinitePlaceQCandidate

namespace InitialThetaSource

namespace PlaceQParameterUniformization

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}
variable {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}

/-- The order law of a `2l`-th-root card: the order of the q-parameter
candidate is `2 * l` times the order of the root q-candidate. -/
theorem twoLRootCard_parameter_order_eq
    (card : QParameterTwoLRootCard l place parameter) :
    (2 * l.value) * card.toQCandidate.order = parameter.order := by
  have hunzero :
      WithZero.unzero parameter.valuation_ne_zero =
        WithZero.unzero card.toQCandidate.valuation_ne_zero ^
          (2 * l.value) := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, WithZero.coe_pow]
    rw [QParameterTwoLRootCard.toQCandidate_q, ← card.root_pow, map_pow]
  apply Int.ofNat_injective
  change
    (((2 * l.value) * Int.toNat card.toQCandidate.exponent : Nat) : Int) =
      ((Int.toNat parameter.exponent : Nat) : Int)
  rw [Nat.cast_mul,
    Int.toNat_of_nonneg (le_of_lt card.toQCandidate.exponent_pos),
    Int.toNat_of_nonneg (le_of_lt parameter.exponent_pos),
    NumberFieldFinitePlace.FinitePlaceQCandidate.exponent,
    NumberFieldFinitePlace.FinitePlaceQCandidate.exponent,
    hunzero, Int.toAdd_pow]
  ring

/-- `2 * l` divides the order of the q-parameter candidate. -/
theorem twoLRootCard_twoL_dvd_parameter_order
    (card : QParameterTwoLRootCard l place parameter) :
    (2 * l.value) ∣ parameter.order :=
  ⟨card.toQCandidate.order, (twoLRootCard_parameter_order_eq card).symm⟩

/-- `l` divides the order of the q-parameter candidate. -/
theorem twoLRootCard_l_dvd_parameter_order
    (card : QParameterTwoLRootCard l place parameter) :
    l.value ∣ parameter.order :=
  ⟨2 * card.toQCandidate.order, by
    rw [← twoLRootCard_parameter_order_eq card]
    ring⟩

/-- A `2l`-th-root card at the same completed place is incompatible with
the clause-(c) condition that `l` is prime to the parameter order: the card
forces `l` to divide the order. The Example 3.2(iv) root is therefore not
a `K_v`-level q-candidate; it is taken after adjoining the root. -/
theorem twoLRootCard_parameter_order_not_coprime
    (card : QParameterTwoLRootCard l place parameter) :
    ¬ Nat.Coprime parameter.order l.value := by
  intro hcop
  have hone : l.value = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop
      (twoLRootCard_l_dvd_parameter_order card) dvd_rfl
  have h5 : 5 ≤ l.value := l.ge_five
  omega

end PlaceQParameterUniformization

namespace PlacePartitionReduction

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-- The frozen D4 Tate-q identification boundary: at every `F`-place `w`
over the bad moduli set, the order of the Tate-card parameter equals the
order of the DVR proxy candidate at the section lift of the moduli place
below `w`. No instance is asserted; this is the recorded boundary between
`BadPlaceTateUniformizationCards.parameter` and `badPlaceQCandidate`. -/
def TateQIdentificationStatement
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    Prop :=
  ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
    (C.parameter w hw).order =
      (badPlaceQCandidate P
        ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w, hw⟩).order

/-- The frozen source-bookkeeping agreement: the source q-parameter order
recorded by `BadPlaceQParameterCards` equals the DVR proxy order at the
section lift of the same moduli place. -/
def SourceQParameterOrderAgreesWithCandidate
    (P : SourcePlaceSelection A) (Q : BadPlaceQParameterCards P) : Prop :=
  ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
    Q.sourceQParameterOrder w hw =
      (badPlaceQCandidate P
        ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w, hw⟩).order

/-- The frozen source-Tate-card agreement: the source q-parameter order
recorded by `BadPlaceQParameterCards` equals the Tate-card parameter order
at the same `F`-place. -/
def SourceOrderAgreesWithTateCard
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (Q : BadPlaceQParameterCards P) : Prop :=
  ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
    Q.sourceQParameterOrder w hw = (C.parameter w hw).order

/-- The proxy value at a bad moduli place, rewritten through the frozen
identification into the Tate-card order. -/
theorem badPlaceQProxy_eq_of_identification
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (h : TateQIdentificationStatement P C)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    badPlaceQProxy P
        ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w, hw⟩ =
      ((NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) w) : Nat) : Real)⁻¹ ^
        (C.parameter w hw).order := by
  rw [badPlaceQProxy, ← h w hw]

/-- On the frozen identification, the DVR proxy order is prime to `l`,
transferred from the Tate card coprimality field. -/
theorem badPlaceQCandidate_order_primeToL_of_identification
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (h : TateQIdentificationStatement P C)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    Nat.Coprime
      (badPlaceQCandidate P
        ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w, hw⟩).order
      l.value := by
  rw [← h w hw]
  exact C.order_coprime w hw

/-- The two frozen agreement propositions compose to the identification
(transitivity of the frozen agreements). -/
theorem tateQIdentification_of_sourceAgreement
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (Q : BadPlaceQParameterCards P)
    (hQ : SourceQParameterOrderAgreesWithCandidate P Q)
    (hC : SourceOrderAgreesWithTateCard P C Q) :
    TateQIdentificationStatement P C := by
  intro w hw
  exact (hC w hw).symm.trans (hQ w hw)

/-- The frozen-agreement triangle: given the frozen identification, the
source-Tate-card agreement transfers to the proxy agreement. -/
theorem sourceQParameterOrderAgrees_of_tateCardAgreement
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (Q : BadPlaceQParameterCards P)
    (h : TateQIdentificationStatement P C)
    (hC : SourceOrderAgreesWithTateCard P C Q) :
    SourceQParameterOrderAgreesWithCandidate P Q := by
  intro w hw
  exact (hC w hw).trans (h w hw)

/-- The frozen-agreement triangle: given the frozen identification, the
proxy agreement transfers to the source-Tate-card agreement. -/
theorem sourceOrderAgreesWithTateCard_of_qParameterAgreement
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (Q : BadPlaceQParameterCards P)
    (h : TateQIdentificationStatement P C)
    (hQ : SourceQParameterOrderAgreesWithCandidate P Q) :
    SourceOrderAgreesWithTateCard P C Q := by
  intro w hw
  exact (hQ w hw).trans (h w hw).symm

end PlacePartitionReduction

end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- D4 Tate-q identification boundary card (conditional). -/
def sourceDefinition31D4TateQIdentification : Obligation :=
  { id := "IUT-I.definition-3.1-D4-tate-q-identification"
    source :=
      "IUT I, Definition 3.1(b)-(c) (corpus 3142-3147, 3180-3184); " ++
        "Example 3.2(iv) (corpus 3701-3726)"
    status := VerificationStatus.conditional
    note :=
      "The D4 Tate-q identification boundary is frozen as three precise " ++
        "statements: `TateQIdentificationStatement` (the Tate-card " ++
        "parameter order equals the DVR proxy order at the section lift " ++
        "of the same moduli place), " ++
        "`SourceQParameterOrderAgreesWithCandidate` (the source " ++
        "bookkeeping order equals the proxy order) and " ++
        "`SourceOrderAgreesWithTateCard` (the source bookkeeping order " ++
        "equals the Tate-card order). The transfer lemmas " ++
        "`badPlaceQProxy_eq_of_identification`, " ++
        "`badPlaceQCandidate_order_primeToL_of_identification` and " ++
        "`tateQIdentification_of_sourceAgreement` are proved " ++
        "conditionally on these statements; no instance is asserted. The " ++
        "frozen-agreement triangle is completed (any two of the three " ++
        "agreements compose to the third). The " ++
        "three closure attempts are recorded: no Tate uniformization " ++
        "theorem is available (Mathlib 4.32.2); finite-place extension " ++
        "scales the order only by the ramification index " ++
        "(`LocalQParameterRamification.order_map`), giving no " ++
        "identification descent; a `2l`-th root in the same completion is " ++
        "incompatible with the prime-to-`l` order condition (see the " ++
        "q-order power kernel card)."
    dependsOn :=
      [ "IUT-I.definition-3.1-D4-supply",
        "IUT-I.definition-3.1-D4-tate-uniformization-identification",
        "Foundations.Geometry.elliptic-tate-uniformization",
        "Foundations.NumberField.local-q-parameter-ramification" ] }

/-- The q-order power kernel card (proved). -/
def sourceDefinition31D4QOrderPowerKernel : Obligation :=
  { id := "IUT-I.definition-3.1-D4-q-order-power-kernel"
    source :=
      "IUT I, Definition 3.1(c) (corpus 3180-3184); Example 3.2(iv) " ++
        "(corpus 3701-3726)"
    status := VerificationStatus.proved
    note :=
      "Unconditional valuation-theoretic kernel of the D4 q-order " ++
        "bookkeeping: `exponent_pow` and `order_pow` (the exponent and " ++
        "order of a positive power of a q-candidate scale by the power), " ++
        "the `2l`-th-root order law `twoLRootCard_parameter_order_eq` " ++
        "((2l) * ord(root) = ord(q)), the divisibility corollaries " ++
        "`twoLRootCard_twoL_dvd_parameter_order` and " ++
        "`twoLRootCard_l_dvd_parameter_order`, and the boundary " ++
        "`twoLRootCard_parameter_order_not_coprime`: a `2l`-th root of " ++
        "the q-parameter candidate in the same completion forces `l` to " ++
        "divide the order, so the Example 3.2(iv) root is not a " ++
        "`K_v`-level q-candidate; it is taken in an extension of the " ++
        "completion."
    dependsOn :=
      [ "Foundations.NumberField.local-q-parameter-ramification",
        "Foundations.NumberField.local-q-parameter-extension" ] }

/-- The q-order transfer kernel card (proved). -/
def sourceDefinition31D4QOrderTransferKernel : Obligation :=
  { id := "IUT-I.definition-3.1-D4-q-order-transfer-kernel"
    source :=
      "IUT I, Definition 3.1(b)-(c) (corpus 3142-3147, 3180-3184): " ++
        "finite-place-extension bookkeeping of the q-parameter orders"
    status := VerificationStatus.proved
    note :=
      "The q-order dimension of the finite-place-extension bookkeeping " ++
        "used by the D4 line: `order_map_eq_self_of_ramificationIdx_eq_one` " ++
        "(an unramified lift preserves the candidate order), " ++
        "`order_dvd_order_map` (the contracted order divides the lifted " ++
        "order), and the coprimality transfer `coprime_order_map_iff` with " ++
        "its two directions (`coprime_order_of_coprime_order_map`, " ++
        "`coprime_order_map_of_coprime`). This is the q-order fragment only; " ++
        "reduction-type fiber uniformity (card " ++
        "`IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap`, subgap (i)) " ++
        "and any Tate-curve statement remain open and are not inferred."
    dependsOn :=
      [ "Foundations.NumberField.local-q-parameter-ramification" ] }

end LeanFormal.IUT.Audit
