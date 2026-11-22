/-
  The most attackable boundary segments of the A2 arithmetic-to-source
  gate: the free layer, and the witness-supply form of the gate.

  The gate `SourceNativeArithmeticToSourceGate`
  (SourceDefinition31Quantifiers.lean:1731; obligation
  `IUT-I.definition-3.1-A2-arithmetic-to-source-gate`, pending) asks, for
  every `A : InitialThetaArithmeticData l`, a native source datum whose
  arithmetic field is `A`.  This file does not close the gate.  It proves
  the two segments that need no new source mathematics:

  * the free layer (section 1): the source entries that the arithmetic
    input already determines - the canonical algebraic-closure extension
    (`F-bar/F`), the square root of -1, the Galois instances, and the
    coprime degree; and
  * the witness-supply reduction (section 2): the gate is *equivalent* to
    the universal supply of the staged clause-construction witness
    `SourceClauseConstructionWitness` (SourceClauseConstructors.lean:1088)
    above every arithmetic datum, by explicit constructions on the
    underlying records.

  Boundary: the D11-E contract-side entry assembly and the D3/D4
  partition line belong to the parallel `ipl-transport-upgrade` work
  (RootLemmas and the SourcePlacePartition leaf) and are not touched
  here.  The A2 gate itself stays pending.

  Placement: HodgeTheater leaf; imports only downwards into
  IUTI/InitialTheta, and no module imports it.
-/

import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open LeanFormal.IUT.InitialThetaSource

noncomputable section

universe u

variable {l : PrimeGeFive}

/-! ## 1. The free layer over the arithmetic input -/

/-- The part of the native source target that the arithmetic input already
determines: the canonical `F-bar/F` entry, the clause-(a) field, and the
Galois and degree facts, re-exposed at the gate's input type. -/
structure InitialThetaArithmeticFreeLayer
    (A : InitialThetaArithmeticData.{u} l) where
  fbar : SourceFbarExtension.{u, u} A
  sqrtNegOne : HasSqrtNegOne A.F
  fmodGalois : IsGalois A.Fmod A.F
  fGaloisK : IsGalois A.F A.K
  degreePrimeToL : Nat.Coprime (Module.finrank A.Fmod A.F) l.value

/-- The free layer of any arithmetic datum, with no source hypothesis. -/
def initialThetaArithmeticFreeLayer
    (A : InitialThetaArithmeticData.{u} l) :
    InitialThetaArithmeticFreeLayer A where
  fbar := SourceFbarExtension.canonical A
  sqrtNegOne := A.tower.sqrtNegOne
  fmodGalois := inferInstance
  fGaloisK := inferInstance
  degreePrimeToL := A.tower.degreePrimeToL

@[simp] theorem initialThetaArithmeticFreeLayer_fbar
    (A : InitialThetaArithmeticData.{u} l) :
    (initialThetaArithmeticFreeLayer A).fbar =
      SourceFbarExtension.canonical A :=
  rfl

@[simp] theorem initialThetaArithmeticFreeLayer_sqrtNegOne
    (A : InitialThetaArithmeticData.{u} l) :
    (initialThetaArithmeticFreeLayer A).sqrtNegOne =
      A.tower.sqrtNegOne :=
  rfl

@[simp] theorem initialThetaArithmeticFreeLayer_degreePrimeToL
    (A : InitialThetaArithmeticData.{u} l) :
    (initialThetaArithmeticFreeLayer A).degreePrimeToL =
      A.tower.degreePrimeToL :=
  rfl

/-! ## 2. The gate as universal witness supply -/

/-- Universal supply of staged clause-construction witnesses over the
arithmetic input. -/
def SourceNativeWitnessSupply (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    ∃ W : SourceClauseConstructionWitness.{u} l, W.arithmetic = A

/-- Forgetting the staged presentation of a native datum. -/
def witnessOfNativeData (T : SourceNativeInitialThetaData.{u} l) :
    SourceClauseConstructionWitness.{u} l where
  arithmetic := T.arithmetic
  fbar := T.tuple.fbar
  signQuotient := T.tuple.source
  clauseA := T.clauseA
  clauseB := T.clauseB
  clauseC := T.clauseC
  clauseD := T.clauseD
  clauseE := T.clauseE
  clauseF := T.clauseF

@[simp] theorem witnessOfNativeData_arithmetic
    (T : SourceNativeInitialThetaData.{u} l) :
    (witnessOfNativeData T).arithmetic = T.arithmetic :=
  rfl

/-- Repackaging a witness through a native datum recovers the witness.
(The other composition records the transported copies carried by
`SourceInitialThetaTuple` and is not claimed here.) -/
@[simp] theorem witnessOfNativeData_sourceData
    (W : SourceClauseConstructionWitness.{u} l) :
    witnessOfNativeData W.sourceData = W :=
  rfl

/-- The A2 gate is exactly the universal supply of staged clause
witnesses: each direction is an explicit construction on the same
underlying fields, and the arithmetic equation is preserved literally. -/
theorem sourceNativeArithmeticToSourceGate_iff_witnessSupply :
    SourceNativeArithmeticToSourceGate.{u} l ↔
      SourceNativeWitnessSupply.{u} l := by
  constructor
  · intro h A
    rcases h A with ⟨T, hT⟩
    exact ⟨witnessOfNativeData T, hT⟩
  · intro h A
    rcases h A with ⟨W, hW⟩
    exact ⟨W.sourceData, hW⟩

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def definition31A2GateReduction : Obligation :=
  { id := "IUT-I.definition-3.1-A2-gate-reduction"
    source :=
      "IUT I, Definition 3.1(a)-(f); A2 gate boundary segments"
    status := VerificationStatus.interface
    note :=
      "Boundary segments of the pending A2 gate: (1) the free layer - " ++
        "the canonical fbar extension, sqrt(-1), the Galois instances, " ++
        "and the coprime-degree fact that InitialThetaArithmeticData " ++
        "determines without new source mathematics; (2) the gate is " ++
        "equivalent to the universal supply of " ++
        "SourceClauseConstructionWitness data, with explicit " ++
        "constructions on both underlying records. The gate itself is " ++
        "not closed: no clause witness is constructed from arithmetic " ++
        "input. Boundary: the D11-E contract-side entry and the D3/D4 " ++
        "partition line are separate (ipl-transport-upgrade)."
    dependsOn :=
      [ "IUT-I.definition-3.1-A2-arithmetic-to-source-gate",
        "IUT-I.definition-3.1-A2-clause-constructors" ] }

end LeanFormal.IUT.Audit
