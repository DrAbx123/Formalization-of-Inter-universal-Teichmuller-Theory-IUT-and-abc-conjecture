/-
  Minimal supply evaluation for `ContractRootSignQuotientSupply` and the
  unit split of the A2 witness supply.

  Paper anchor (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`, Definition 3.1, extraction lines 3123-3283):
  initial Theta-data is the tuple (F-bar/F, X_F, l, C_K, V, V^bad_mod,
  epsilon) subject to clauses (a)--(f).  Clause (b) (lines 3131-3157)
  forms C_F as "the stack-theoretic quotient of X_F by the unique
  F-involution '-1'"; it asks V^bad_mod to be a nonempty set of
  nonarchimedean valuations of F_mod of odd residue characteristic at
  which X_F has bad (multiplicative) reduction.  Clause (d) (lines
  3185-3215) fixes C_K = C_F x_F K and the K-level orbicurves; clause (e)
  (lines 3216-3226) makes V a section of V(K) -> V_mod; clause (f)
  (lines 3273-3283) binds the cusp epsilon.

  This file separates the supply of `SourceSignQuotientData` into the two
  record parts the repository already carries, proves the place part
  outright, and reduces the remaining question to one named card:

  * Section 1: every number field has a finite place of odd residue
    characteristic, i.e. a maximal ideal above an odd rational prime;
  * Section 2: `SourceSignQuotientData` projects to
    `SourceSignQuotientGeometricCore` (SourceSignQuotientConstruction
    .lean:30) and to `SourcePlaceSelection`; assembling the parts back
    through `toSourceSignQuotientData` is a two-sided roundtrip;
  * Section 3: contract-root sign-quotient supply is therefore
    equivalent to geometric-core supply at contract roots, and -- given
    contract-root supply -- to arithmetic-level geometric-core supply.
    The residual card is the geometric core alone: the represented
    orbicurves, sign action, quotient witness, group data and cusp; no
    constructor of these foundation objects exists in the repository;
  * Section 4: the A2 gate is equivalent to supplying, over each
    arithmetic root, a sign quotient together with a clause assembly
    over it, the F-bar/F entry being canonical.  The assembly is the
    second named unit, conditional on the quotient; only its
    sufficiency is claimed.

  Boundary: the D11-E contract-side entry and the D3/D4 partition line
  (ipl-transport-upgrade) are untouched, and no module of the RootLemmas
  line is imported.  Placement: HodgeTheater leaf; no module imports it.
-/

import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31A2GateReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import Mathlib.RingTheory.Ideal.Int

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source

noncomputable section

universe u

variable {l : PrimeGeFive}

/-! ## 1. Odd-residue-characteristic finite places exist -/

/-- Every number field has a finite place of odd residue characteristic:
the place given by a maximal ideal above an odd rational prime.  This is
the arithmetic content of the selected-place half of the source record
(Definition 3.1(b), extraction lines 3142-3145). -/
theorem NumberFieldFinitePlace.exists_odd_residueCharacteristic
    (K : Type u) [Field K] [NumberField K] :
    ∃ place : NumberField.FinitePlace K,
      Odd (NumberFieldFinitePlace.residueCharacteristic place) := by
  obtain ⟨p, hp3, hpprime⟩ := Nat.exists_infinite_primes 3
  have hpne2 : p ≠ 2 := by
    rintro rfl
    omega
  haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := NumberField.RingOfIntegers K)
      (P := Ideal.span {(p : ℤ)})
  have hp_mem : ((p : ℕ) : NumberField.RingOfIntegers K) ∈ Q := by
    have hspan : (p : ℤ) ∈ Ideal.span {(p : ℤ)} :=
      Ideal.mem_span_singleton_self (p : ℤ)
    have hunder : (p : ℤ) ∈ Q.under ℤ := hQover.over.le hspan
    have hmap :
        algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) ∈ Q := by
      simpa only [Ideal.under_def, Ideal.mem_comap] using hunder
    simpa using hmap
  haveI : Q.IsMaximal := hQmax
  haveI : Field (NumberField.RingOfIntegers K ⧸ Q) :=
    Ideal.Quotient.field Q
  have hquot : ((p : ℕ) : NumberField.RingOfIntegers K ⧸ Q) = 0 := by
    have hmk : Ideal.Quotient.mk Q
        ((p : ℕ) : NumberField.RingOfIntegers K) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hp_mem
    exact (map_natCast (Ideal.Quotient.mk Q) p).symm.trans hmk
  have hchar : ringChar (NumberField.RingOfIntegers K ⧸ Q) = p :=
    CharP.ringChar_of_prime_eq_zero hpprime hquot
  let primeQ :
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    { asIdeal := Q
      isPrime := hQmax.isPrime
      ne_bot :=
        Ring.ne_bot_of_isMaximal_of_not_isField hQmax
          (NumberField.RingOfIntegers.not_isField K) }
  refine ⟨NumberField.FinitePlace.mk primeQ, ?_⟩
  have hres : NumberFieldFinitePlace.residueCharacteristic
      (NumberField.FinitePlace.mk primeQ) = p := by
    dsimp only [NumberFieldFinitePlace.residueCharacteristic,
      NumberFieldFinitePlace.ResidueField,
      NumberFieldFinitePlace.underlyingPrime]
    have hmk : NumberField.FinitePlace.maximalIdeal
        (NumberField.FinitePlace.mk primeQ) = primeQ :=
      NumberField.FinitePlace.maximalIdeal_mk primeQ
    have hmem : ((p : ℕ) : NumberField.RingOfIntegers K) ∈
        (NumberField.FinitePlace.mk primeQ).maximalIdeal.asIdeal := by
      rw [hmk]
      exact hp_mem
    exact CharP.ringChar_of_prime_eq_zero hpprime
      ((map_natCast
        (Ideal.Quotient.mk
          (NumberField.FinitePlace.mk primeQ).maximalIdeal.asIdeal) p).symm.trans
        (Ideal.Quotient.eq_zero_iff_mem.mpr hmem))
  rw [hres]
  exact hpprime.odd_of_ne_two hpne2
/-! ## 2. The sign-quotient datum splits into core and selected places -/

/-- Projection of the source sign-quotient datum onto its geometric core:
the represented orbicurves, the sign action and quotient witness, the
finite-etale group data, the scalar extensions and the boundary cusp. -/
def geometricCoreOfSignQuotientData
    {A : InitialThetaArithmeticData.{u} l}
    (D : SourceSignQuotientData A) :
    SourceSignQuotientGeometricCore A where
  xF := D.xF
  xF_geometry := D.xF_geometry
  ellipticInvolution := D.ellipticInvolution
  ellipticInvolution_squared := D.ellipticInvolution_squared
  unique_elliptic_involution := D.unique_elliptic_involution
  signAction := D.signAction
  signAction_inversion_eq_ellipticInvolution :=
    D.signAction_inversion_eq_ellipticInvolution
  cF := D.cF
  quotient := D.quotient
  quotientWitness := D.quotientWitness
  xFGroups := D.xFGroups
  cFGroups := D.cFGroups
  fGroupInclusion := D.fGroupInclusion
  xK := D.xK
  cK := D.cK
  xKExtension := D.xKExtension
  cKExtension := D.cKExtension
  xKType := D.xKType
  cKType := D.cKType
  xK_eq_extension := D.xK_eq_extension
  cK_eq_extension := D.cK_eq_extension
  epsilon := D.epsilon

/-- Projection of the source sign-quotient datum onto the selected-place
record: the moduli bad-place set, its odd-residue-characteristic proof and
its nonemptiness. -/
def placeSelectionOfSignQuotientData
    {A : InitialThetaArithmeticData.{u} l}
    (D : SourceSignQuotientData A) :
    SourcePlaceSelection A where
  V_mod_bad := D.V_mod_bad
  V_mod_bad_odd_residue_characteristic :=
    D.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := D.V_mod_bad_nonempty

@[simp] theorem geometricCoreOfSignQuotientData_toSourceSignQuotientData
    {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    geometricCoreOfSignQuotientData (G.toSourceSignQuotientData P) = G :=
  rfl

@[simp] theorem placeSelectionOfSignQuotientData_toSourceSignQuotientData
    {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    placeSelectionOfSignQuotientData (G.toSourceSignQuotientData P) = P :=
  rfl

/-- Over any arithmetic root, the sign-quotient record is supplied exactly
when both its geometric core and its selected-place record are. -/
theorem nonempty_sourceSignQuotientData_iff_core_and_selection
    (A : InitialThetaArithmeticData.{u} l) :
    Nonempty (SourceSignQuotientData A) ↔
      Nonempty (SourceSignQuotientGeometricCore A) ∧
        Nonempty (SourcePlaceSelection A) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨⟨geometricCoreOfSignQuotientData D⟩,
      ⟨placeSelectionOfSignQuotientData D⟩⟩
  · rintro ⟨hG, hP⟩
    obtain ⟨G⟩ := hG
    obtain ⟨P⟩ := hP
    exact ⟨G.toSourceSignQuotientData P⟩

/-! ## 3. Supply of the record reduces to the geometric core -/

/-- The selected-place record over any arithmetic datum, built from an
odd-residue-characteristic place of `Fmod`.  This supplies exactly the
three fields of `SourcePlaceSelection`; the bad-reduction condition of
Definition 3.1(b) is not asserted. -/
def placeSelectionOfArithmeticData
    (A : InitialThetaArithmeticData.{u} l) :
    SourcePlaceSelection A := by
  let h := NumberFieldFinitePlace.exists_odd_residueCharacteristic A.Fmod
  exact SourcePlaceSelection.singleton A (Classical.choose h)
    (Classical.choose_spec h)

theorem sourcePlaceSelectionNonempty
    (A : InitialThetaArithmeticData.{u} l) :
    Nonempty (SourcePlaceSelection A) :=
  ⟨placeSelectionOfArithmeticData A⟩

/-- The selected-place half of the source record is unconditional. -/
def SourcePlaceSelectionSupply (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l, Nonempty (SourcePlaceSelection A)

theorem sourcePlaceSelectionSupply :
    SourcePlaceSelectionSupply.{u} l :=
  fun A => sourcePlaceSelectionNonempty A

/-- The source sign-quotient record is supplied over every arithmetic
datum. -/
def SourceSignQuotientSupply (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l, Nonempty (SourceSignQuotientData A)

/-- Supply of the geometric core of the source sign-quotient record over
every arithmetic datum. -/
def SourceSignQuotientGeometricCoreSupply (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty (SourceSignQuotientGeometricCore A)

/-- Supply of the geometric core over the arithmetic roots of contracts. -/
def SourceSignQuotientGeometricCoreSupplyAtContractRoots
    (l : PrimeGeFive) : Prop :=
  ∀ S : SourceDefinition31Data.{u} l,
    Nonempty (SourceSignQuotientGeometricCore S.arithmetic)

/-- The full sign-quotient supply is exactly the geometric-core supply:
the place half is satisfied by the canonical selected-place record. -/
theorem sourceSignQuotientSupply_iff_geometricCoreSupply :
    SourceSignQuotientSupply.{u} l ↔
      SourceSignQuotientGeometricCoreSupply.{u} l := by
  constructor
  · intro h A
    obtain ⟨D⟩ := h A
    exact ⟨geometricCoreOfSignQuotientData D⟩
  · intro h A
    obtain ⟨G⟩ := h A
    exact ⟨G.toSourceSignQuotientData (placeSelectionOfArithmeticData A)⟩

/-- Contract-root sign-quotient supply is exactly geometric-core supply
at contract roots. -/
theorem contractRootSignQuotientSupply_iff_geometricCoreSupplyAtContractRoots :
    ContractRootSignQuotientSupply.{u} l ↔
      SourceSignQuotientGeometricCoreSupplyAtContractRoots.{u} l := by
  constructor
  · intro h S
    obtain ⟨D⟩ := h S
    exact ⟨geometricCoreOfSignQuotientData D⟩
  · intro h S
    obtain ⟨G⟩ := h S
    exact ⟨G.toSourceSignQuotientData
      (placeSelectionOfArithmeticData S.arithmetic)⟩

/-- Given contract-root supply, contract-root sign-quotient supply is the
arithmetic-level geometric-core supply. -/
theorem contractRootSignQuotientSupply_iff_geometricCoreSupply
    (hR : SourceContractRootSupply.{u} l) :
    ContractRootSignQuotientSupply.{u} l ↔
      SourceSignQuotientGeometricCoreSupply.{u} l := by
  constructor
  · intro h A
    obtain ⟨S, hS⟩ := hR A
    obtain ⟨D⟩ := h S
    exact ⟨hS ▸ geometricCoreOfSignQuotientData D⟩
  · intro h S
    obtain ⟨G⟩ := h S.arithmetic
    exact ⟨G.toSourceSignQuotientData
      (placeSelectionOfArithmeticData S.arithmetic)⟩

/-! ## 4. The A2 witness supply: sign quotient plus clause assembly -/

/-- The six source clauses over a fixed arithmetic root and sign quotient,
exactly the clause fields of `SourceClauseConstructionWitness` after the
arithmetic root and the canonical `F-bar/F` entry are removed. -/
structure SourceClauseAssembly
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (SQ : SourceSignQuotientData A) where
  clauseA : SourceClauseA A SQ
  clauseB : SourceClauseB A SQ clauseA
  clauseC : SourceClauseC A SQ clauseA clauseB
  clauseD : SourceClauseD A SQ clauseA clauseB clauseC
  clauseE : SourceClauseE A SQ clauseA clauseB clauseC clauseD
  clauseF : SourceClauseF A SQ clauseA clauseB clauseC clauseD clauseE

def clauseAssemblyOfWitness
    (W : SourceClauseConstructionWitness.{u} l) :
    SourceClauseAssembly W.arithmetic W.signQuotient where
  clauseA := W.clauseA
  clauseB := W.clauseB
  clauseC := W.clauseC
  clauseD := W.clauseD
  clauseE := W.clauseE
  clauseF := W.clauseF

/-- The free `F-bar/F` entry is the canonical extension, so a sign quotient
plus its clause assembly rebuilds a full staged witness. -/
def witnessOfClauseAssembly
    (A : InitialThetaArithmeticData.{u} l)
    (SQ : SourceSignQuotientData A)
    (assembly : SourceClauseAssembly A SQ) :
    SourceClauseConstructionWitness.{u} l where
  arithmetic := A
  fbar := SourceFbarExtension.canonical A
  signQuotient := SQ
  clauseA := assembly.clauseA
  clauseB := assembly.clauseB
  clauseC := assembly.clauseC
  clauseD := assembly.clauseD
  clauseE := assembly.clauseE
  clauseF := assembly.clauseF

@[simp] theorem witnessOfClauseAssembly_arithmetic
    (A : InitialThetaArithmeticData.{u} l)
    (SQ : SourceSignQuotientData A)
    (assembly : SourceClauseAssembly A SQ) :
    (witnessOfClauseAssembly A SQ assembly).arithmetic = A :=
  rfl

/-- The A2 witness supply is exactly the supply, over each arithmetic root,
of a sign quotient together with a clause assembly over it. -/
theorem sourceNativeWitnessSupply_iff_clauseAssembly :
    SourceNativeWitnessSupply.{u} l ↔
      ∀ A : InitialThetaArithmeticData.{u} l,
        ∃ SQ : SourceSignQuotientData A,
          Nonempty (SourceClauseAssembly.{u} A SQ) := by
  constructor
  · intro h A
    obtain ⟨W, hW⟩ := h A
    have h0 :
        ∃ SQ : SourceSignQuotientData W.arithmetic,
          Nonempty (SourceClauseAssembly W.arithmetic SQ) :=
      ⟨W.signQuotient, ⟨clauseAssemblyOfWitness W⟩⟩
    exact hW ▸ h0
  · intro h A
    obtain ⟨SQ, hne⟩ := h A
    obtain ⟨assembly⟩ := hne
    exact ⟨witnessOfClauseAssembly A SQ assembly, rfl⟩

/-- Supply of a clause assembly over every arithmetic root and every sign
quotient. -/
def SourceClauseAssemblySupply (l : PrimeGeFive) : Prop :=
  ∀ (A : InitialThetaArithmeticData.{u} l) (SQ : SourceSignQuotientData A),
    Nonempty (SourceClauseAssembly A SQ)

/-- The sign-quotient half of the witness supply is necessary. -/
theorem sourceNativeWitnessSupply_implies_signQuotientSupply
    (h : SourceNativeWitnessSupply.{u} l) :
    SourceSignQuotientSupply.{u} l := by
  intro A
  obtain ⟨W, hW⟩ := h A
  exact ⟨hW ▸ W.signQuotient⟩

/-- Sign-quotient supply plus assembly supply yields the witness supply;
the `F-bar/F` entry is absorbed by its canonical construction. -/
theorem sourceNativeWitnessSupply_of_signQuotientSupply_of_clauseAssemblySupply
    (hS : SourceSignQuotientSupply.{u} l)
    (hA : SourceClauseAssemblySupply.{u} l) :
    SourceNativeWitnessSupply.{u} l := by
  intro A
  obtain ⟨SQ⟩ := hS A
  obtain ⟨assembly⟩ := hA A SQ
  exact ⟨witnessOfClauseAssembly A SQ assembly, rfl⟩

/-- The A2 gate, restated on the two units: over each arithmetic root, a
sign quotient together with a clause assembly over it. -/
theorem sourceNativeArithmeticToSourceGate_iff_clauseAssembly :
    SourceNativeArithmeticToSourceGate.{u} l ↔
      ∀ A : InitialThetaArithmeticData.{u} l,
        ∃ SQ : SourceSignQuotientData A,
          Nonempty (SourceClauseAssembly.{u} A SQ) :=
  (sourceNativeArithmeticToSourceGate_iff_witnessSupply (l := l)).trans
    sourceNativeWitnessSupply_iff_clauseAssembly

/-- With the geometric-core card and the assembly unit supplied, the A2
gate follows. -/
theorem sourceNativeArithmeticToSourceGate_of_units
    (hG : SourceSignQuotientGeometricCoreSupply.{u} l)
    (hA : SourceClauseAssemblySupply.{u} l) :
    SourceNativeArithmeticToSourceGate.{u} l :=
  (sourceNativeArithmeticToSourceGate_iff_witnessSupply (l := l)).mpr
    (sourceNativeWitnessSupply_of_signQuotientSupply_of_clauseAssemblySupply
      ((sourceSignQuotientSupply_iff_geometricCoreSupply (l := l)).mpr hG)
      hA)

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def definition31SignQuotientSupplyReduction : Obligation :=
  { id := "IUT-I.definition-3.1-sign-quotient-supply-reduction"
    source :=
      "IUT I, Definition 3.1(b),(d),(e),(f); extraction lines 3123-3283"
    status := VerificationStatus.interface
    note :=
      "Minimal supply evaluation for ContractRootSignQuotientSupply. " ++
        "Proved: (1) SourceSignQuotientData splits, by literal " ++
        "projections and a two-sided roundtrip, into " ++
        "SourceSignQuotientGeometricCore and SourcePlaceSelection; " ++
        "(2) every number field has a finite place of odd residue " ++
        "characteristic, so the selected-place half of the record is " ++
        "unconditional (the record does not assert bad reduction; that " ++
        "condition stays in clause (b)); (3) contract-root sign-quotient " ++
        "supply is equivalent to geometric-core supply at contract roots " ++
        "and, modulo SourceContractRootSupply, to arithmetic-level " ++
        "geometric-core supply; (4) the A2 gate is equivalent to " ++
        "supplying, over each arithmetic root, a sign quotient together " ++
        "with a clause assembly over it, the F-bar/F entry being " ++
        "canonical.  Residual card: the geometric-core supply; no " ++
        "constructor of these foundation objects exists in the " ++
        "repository.  Second unit: the clause assembly, conditional on " ++
        "the sign quotient; only sufficiency is claimed.  Boundary: no " ++
        "RootLemmas import; D11-E and D3/D4 untouched.  Consumers: " ++
        "SourceHodgeTheaterBridge, D3.1 SourceOriginalInput, " ++
        "SourceH1H2Construction."
    dependsOn :=
      [ "IUT-I.definition31-carrier-consolidation",
        "IUT-I.definition-3.1-A2-gate-reduction",
        "IUT-I.definition-3.1-A2-sign-quotient-place-binding" ] }

end LeanFormal.IUT.Audit
