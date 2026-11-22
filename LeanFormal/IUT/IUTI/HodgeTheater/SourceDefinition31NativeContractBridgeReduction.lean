/-
  Native-versus-contract record bridge for the "current side" of IUT I
  Definition 3.1: three construction routes, their provable fragments, and
  the exact points at which each route halts.

  Paper anchor (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`, extraction line 3122): initial Theta-data is
  the tuple (F-bar/F, X_F, l, C_K, V, V^bad_mod, epsilon) subject to
  clauses (a)--(f).

  Carriers compared here:
  * `SourceNativeInitialThetaData` (SourceDefinition31Quantifiers.lean:1640):
    arithmetic data plus the actual foundation objects of the tuple and the
    six dependent source clauses.
  * `SourceDefinition31Data` (SourceDefinition31Boundary.lean:660): the
    abstract contract; its clause carriers are plain types.
  * `SourcePlaceSelection` (SourcePlaceSelection.lean:31): the
    selected-place record whose three fields are a literal prefix of
    `SourceSignQuotientData`; it is the input type of the pending D11-E
    entry assembly.

  All statements below are made at one universe level: every carrier is
  pinned to `.{u}`, so the three records are compared at the same level.

  Routes (section numbers below):

  (A) native -> record -> contract.  Proved: the native side projects to
      `SourcePlaceSelection` (section 2) and supplies the first two
      partition fields `badIncluded`/`selectedNonempty` of a place
      partition fragment (section 3).  The assembly then halts at the
      finite bad support, the Nat labels, the real q-parameter layer, and
      every later clause.  Given the A2 gate, a root-preserving
      native-to-contract bridge is *equivalent* to supplying contract
      instances above every arithmetic root (section 4).
  (B) contract -> record -> native.  Proved: the contract supplies its
      arithmetic field and the canonical algebraic-closure extension
      (section 5); the assembly halts at the first foundation object
      `x_F : HyperbolicOrbicurve F`.  A root-preserving contract-to-native
      bridge is *equivalent* to pointwise A2-totalization over contract
      roots; together with contract-root supply it would close the A2 gate.
  (C) mediation through an intermediate record projecting to contracts.
      Proved: such a route yields route (A) directly and hence removes no
      obstruction (section 6); this instantiates to the dual-contract
      alignment (SourceDefinition31DualContractAlignment.lean:139), whose
      `current` field is a contract.

  Nothing here invents carrier fields: every constructed object is a
  projection or the canonical extension.  Filling the contract's free
  slots (labels, reduction predicates) with degenerate constants is
  rejected (report section 19).  The cards for the cross-contract gap
  items stay in the report (sections 18/19); consumers:
  `SourceDefinition31Data.toInitialThetaInput` (Boundary:822) ->
  OriginalInput:44-45, SourceH1H2Construction:275-277,
  SourceHodgeTheaterBridge.

  Placement: HodgeTheater leaf beside the carrier-consolidation leaf; it
  imports downwards only, and no module imports it.
-/

import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open LeanFormal.IUT.InitialThetaSource
open Theorem311Source

noncomputable section

universe u w

variable {l : PrimeGeFive}

/-! ## 1. The shared arithmetic root -/

/-- Native projection onto the root shared with the abstract contract. -/
def nativeRecordBridgeArithmetic
    (T : SourceNativeInitialThetaData.{u} l) :
    InitialThetaArithmeticData.{u} l :=
  T.arithmetic

theorem nativeRecordBridgeArithmetic_spec
    (T : SourceNativeInitialThetaData.{u} l) :
    nativeRecordBridgeArithmetic T = T.arithmetic :=
  rfl

/-- Contract projection onto the same root. -/
def contractRecordBridgeArithmetic
    (S : SourceDefinition31Data.{u} l) :
    InitialThetaArithmeticData.{u} l :=
  S.arithmetic

theorem contractRecordBridgeArithmetic_spec
    (S : SourceDefinition31Data.{u} l) :
    contractRecordBridgeArithmetic S = S.arithmetic :=
  rfl

/-! ## 2. Route A: the native projection onto the selected-place record -/

/-- The native carrier feeds the D11-E selected-place input by projection:
the three fields of `SourcePlaceSelection` are fields of the same sign
quotient record, so this step needs no new mathematics. -/
def nativePlaceSelection
    (T : SourceNativeInitialThetaData.{u} l) :
    SourcePlaceSelection T.arithmetic where
  V_mod_bad := T.tuple.source.V_mod_bad
  V_mod_bad_odd_residue_characteristic :=
    T.tuple.source.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := T.tuple.source.V_mod_bad_nonempty

@[simp] theorem nativePlaceSelection_V_mod_bad
    (T : SourceNativeInitialThetaData.{u} l) :
    (nativePlaceSelection T).V_mod_bad = T.tuple.source.V_mod_bad :=
  rfl

theorem nativePlaceSelection_odd_residue_characteristic
    (T : SourceNativeInitialThetaData.{u} l)
    (p : NumberField.FinitePlace T.arithmetic.Fmod)
    (hp : p ∈ (nativePlaceSelection T).V_mod_bad) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  T.tuple.source.V_mod_bad_odd_residue_characteristic p hp

theorem nativePlaceSelection_nonempty
    (T : SourceNativeInitialThetaData.{u} l) :
    (nativePlaceSelection T).V_mod_bad.Nonempty :=
  T.tuple.source.V_mod_bad_nonempty

/-! ## 3. Route A: the first partition fields -/

/-- The fragment of a place partition reachable from native data: the two
carried fields `badIncluded` and `selectedNonempty`, with the selected and
bad carriers chosen as the native place sets.  The contract's
`SourcePlacePartition` (Boundary:39) asks in addition for `Fintype Bad`
and two `Nat` labels with the compatibility law; none of those is
derivable from the native carriers, so no partition is assembled here. -/
structure NativeContractPartitionFragment (l : PrimeGeFive) where
  selectedPlaces : Type u
  badPlaces : Type u
  badIncluded : badPlaces → selectedPlaces
  selectedNonempty : Nonempty selectedPlaces

namespace NativeContractPartitionFragment

/-- Construction of the fragment from a native datum: the bad inclusion is
the native place bijection composed with the finite-place embedding. -/
def ofNative (T : SourceNativeInitialThetaData.{u} l) :
    NativeContractPartitionFragment.{u} l where
  selectedPlaces :=
    {v : NumberFieldPlace T.arithmetic.K // v ∈ T.tuple.source.V}
  badPlaces :=
    {p : NumberField.FinitePlace T.arithmetic.Fmod //
      p ∈ T.tuple.source.V_mod_bad}
  badIncluded := fun b =>
    T.tuple.source.V_mod_bijection (NumberFieldPlace.finite b.1)
  selectedNonempty := by
    rcases T.tuple.source.V_mod_bad_nonempty with ⟨p, _hp⟩
    exact ⟨T.tuple.source.V_mod_bijection (NumberFieldPlace.finite p)⟩

/-- The bad inclusion is injective: the finite-place embedding is
injective and the native place bijection is an equivalence. -/
theorem ofNative_badIncluded_injective
    (T : SourceNativeInitialThetaData.{u} l) :
    Function.Injective (ofNative T).badIncluded := by
  intro a b h
  have h₁ : NumberFieldPlace.finite a.1 =
      NumberFieldPlace.finite b.1 :=
    T.tuple.source.V_mod_bijection.injective h
  have h₂ : a.1 = b.1 := by
    injection h₁
  exact Subtype.ext h₂

end NativeContractPartitionFragment

/-! ## 4. Route A: root-preserving bridges and root supply -/

/-- Existence of a native-to-contract record bridge preserving the
arithmetic root; the precise statement analyzed by the three routes. -/
def NativeContractRecordBridge (l : PrimeGeFive) : Prop :=
  ∃ Φ : SourceNativeInitialThetaData.{u} l → SourceDefinition31Data.{u} l,
    ∀ T, (Φ T).arithmetic = T.arithmetic

/-- Existence of a contract instance above every arithmetic root. -/
def SourceContractRootSupply (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    ∃ S : SourceDefinition31Data.{u} l, S.arithmetic = A

/-- Route A, positive direction: a bridge together with the A2 gate
supplies a contract instance above every arithmetic root. -/
theorem contractRootSupply_of_nativeContractRecordBridge_of_gate
    (hG : SourceNativeArithmeticToSourceGate.{u} l)
    (hB : NativeContractRecordBridge.{u} l) :
    SourceContractRootSupply.{u} l := by
  intro A
  rcases hB with ⟨Φ, hΦ⟩
  rcases hG A with ⟨T, hT⟩
  exact ⟨Φ T, (hΦ T).trans hT⟩

/-- Route A, converse direction: root supply alone yields the bridge, by
choosing one contract instance above each root. -/
theorem nativeContractRecordBridge_of_contractRootSupply
    (hR : SourceContractRootSupply.{u} l) :
    NativeContractRecordBridge.{u} l :=
  ⟨fun T => (hR T.arithmetic).choose,
    fun T => (hR T.arithmetic).choose_spec⟩

/-- Route A verdict: modulo the A2 gate the native-to-contract bridge is
exactly contract-root supply; no record mediation with less content can
replace either side. -/
theorem nativeContractRecordBridge_iff_contractRootSupply_of_gate
    (hG : SourceNativeArithmeticToSourceGate.{u} l) :
    NativeContractRecordBridge.{u} l ↔
      SourceContractRootSupply.{u} l :=
  ⟨contractRootSupply_of_nativeContractRecordBridge_of_gate hG,
    nativeContractRecordBridge_of_contractRootSupply⟩

/-! ## 5. Route B: contract-to-native and pointwise totalization -/

/-- Existence of a contract-to-native record bridge preserving the root. -/
def ContractNativeRecordBridge (l : PrimeGeFive) : Prop :=
  ∃ Ψ : SourceDefinition31Data.{u} l → SourceNativeInitialThetaData.{u} l,
    ∀ S, (Ψ S).arithmetic = S.arithmetic

/-- Pointwise A2-totalization over contract roots: every contract instance
has a native totalization above its own arithmetic root. -/
def PointwiseNativeTotalizationOverContractRoots
    (l : PrimeGeFive) : Prop :=
  ∀ S : SourceDefinition31Data.{u} l,
    ∃ T : SourceNativeInitialThetaData.{u} l,
      T.arithmetic = S.arithmetic

/-- Route B verdict: the root-preserving bridge is exactly pointwise
totalization.  One direction applies the bridge to each contract; the
other chooses a totalization per contract, so the bridge carries no
content beyond the displayed pointwise statement. -/
theorem contractNativeRecordBridge_iff_pointwiseTotalization :
    ContractNativeRecordBridge.{u} l ↔
      PointwiseNativeTotalizationOverContractRoots.{u} l :=
  ⟨fun hB => by
      rcases hB with ⟨Ψ, hΨ⟩
      exact fun S => ⟨Ψ S, hΨ S⟩,
    fun h => ⟨fun S => (h S).choose, fun S => (h S).choose_spec⟩⟩

/-- Route B carries the A2 content: together with contract-root supply, a
contract-to-native bridge closes the A2 gate itself. -/
theorem sourceNativeGate_of_contractNativeBridge_of_contractRootSupply
    (hR : SourceContractRootSupply.{u} l)
    (hB : ContractNativeRecordBridge.{u} l) :
    SourceNativeArithmeticToSourceGate.{u} l := by
  intro A
  rcases hR A with ⟨S, hS⟩
  rcases hB with ⟨Ψ, hΨ⟩
  exact ⟨Ψ S, (hΨ S).trans hS⟩

/-- The first block route B meets: a sign quotient over each contract root.
The first field of that record is the foundation orbicurve `x_F`, which no
contract field supplies.  This is the named card `contract-root sign
quotient supply`; the implication below shows it is a necessary block. -/
def ContractRootSignQuotientSupply (l : PrimeGeFive) : Prop :=
  ∀ S : SourceDefinition31Data.{u} l,
    Nonempty (SourceSignQuotientData S.arithmetic)

theorem contractNativeRecordBridge_implies_signQuotientSupply
    (hB : ContractNativeRecordBridge.{u} l) :
    ContractRootSignQuotientSupply.{u} l := by
  intro S
  rcases hB with ⟨Ψ, hΨ⟩
  exact ⟨(hΨ S) ▸ (Ψ S).tuple.source⟩

/-- The part of route B that does go through: the contract's own
arithmetic root carries the canonical algebraic-closure extension, i.e. the
`F-bar/F` entry of the source tuple. -/
def contractCanonicalFbar (S : SourceDefinition31Data.{u} l) :
    SourceFbarExtension S.arithmetic :=
  SourceFbarExtension.canonical S.arithmetic

theorem contractCanonicalFbar_spec
    (S : SourceDefinition31Data.{u} l) :
    contractCanonicalFbar S =
      SourceFbarExtension.canonical S.arithmetic :=
  rfl

/-! ## 6. Route C: mediation through an intermediate record -/

/-- Any mediating record whose projection to the contract produces
root-preserving data yields the route-A bridge directly, so record
mediation removes no obstruction.  Instantiation: the dual-contract
alignment `Definition31DualContractAlignment` carries a
`current : SourceDefinition31Data l` field, so a bridge through alignments
is at least as hard as route A. -/
theorem nativeContractRecordBridge_of_mediatingProjection
    {M : Type w} (π : M → SourceDefinition31Data.{u} l)
    (h : ∃ Φ : SourceNativeInitialThetaData.{u} l → M,
      ∀ T, (π (Φ T)).arithmetic = T.arithmetic) :
    NativeContractRecordBridge.{u} l := by
  rcases h with ⟨Φ, hΦ⟩
  exact ⟨fun T => π (Φ T), hΦ⟩

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def definition31NativeContractBridgeReduction : Obligation :=
  { id := "IUT-I.definition-3.1-native-contract-record-bridge"
    source :=
      "IUT I, Definition 3.1 (extraction line 3122); native-versus-" ++
        "contract record bridge, routes A-C"
    status := VerificationStatus.interface
    note :=
      "Route fragments proved: the native carrier projects to " ++
        "SourcePlaceSelection and supplies badIncluded/selectedNonempty " ++
        "of a partition fragment; the contract side supplies its " ++
        "arithmetic root and the canonical fbar extension. Route " ++
        "verdicts proved: native-to-contract bridges are, modulo the A2 " ++
        "gate, equivalent to contract-root supply; contract-to-native " ++
        "bridges are equivalent to pointwise A2-totalization and, with " ++
        "root supply, would close the A2 gate; mediation through records " ++
        "projecting to contracts yields route A directly. No bridge is " ++
        "constructed and no carrier field is invented; the remaining " ++
        "blocks are the contract's finite bad support and Nat labels, " ++
        "the real q-parameter layer, and the foundation orbicurve " ++
        "objects. Consumers: OriginalInput:44-45, " ++
        "SourceH1H2Construction:275-277, SourceHodgeTheaterBridge; the " ++
        "D11-E entry assembly consumes the SourcePlaceSelection " ++
        "projection. Cards: report sections 18-19."
    dependsOn :=
      [ "IUT-I.definition31-carrier-consolidation",
        "IUT-I.definition31-contract-alignment",
        "IUT-I.definition-3.1-A2-arithmetic-to-source-gate" ] }

end LeanFormal.IUT.Audit
