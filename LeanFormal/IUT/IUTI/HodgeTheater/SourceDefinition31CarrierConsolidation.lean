/-
  Carrier consolidation for the Definition 3.1 "current side".

  Paper anchor: IUT I, Definition 3.1 (extraction line 3122: initial
  Theta-data is the tuple (F-bar/F, X_F, l, C_K, V, V^bad_mod, epsilon)
  subject to clauses (a)--(f); line numbers below use the extraction of
  `D:\lean\papers\motizuki_corpus\text\Inter-universal Teichmuller
  Theory I.txt`).

  Three in-repo carriers model that single source object on the current
  side.  Their contract-level comparison (fields, dependency direction,
  consumers) is recorded here together with the provable bridges.

  * `Theorem311Source.SourceDefinition31Data`
    (SourceDefinition31Boundary.lean:660): the contract itself; 18
    fields (arithmetic; selectedPlaces/badPlaces; reduction; torsion;
    orbicurve; sections; cusp; five opaque compatibility slots with
    proofs).  Consumer-facing contract.
  * `Theorem311Source.SourceDefinition31Root.Definition31StageKernel.
    StageConstructionTrace` (SourceDefinition31RootLemmas.lean:3776):
    the same 18 fields plus a duplicated `partition` together with
    `partition_alignment` forcing it equal to `reduction.partition`.
    Proved here: information-equivalent to the contract (Sections 1-2);
    the duplicated slot is forced, so no consumer can observe a
    difference.
  * `InitialThetaSource.SourceNativeInitialThetaData`
    (SourceDefinition31Quantifiers.lean:1640): arithmetic plus a tuple
    of actual foundation objects (algebraic-closure extension, hyperbolic
    orbicurves over F and K, place sets, boundary cusp) and six dependent
    source clauses.  Not equivalent to the abstract contract: the
    carriers are foundation objects against abstract types, so a bridge
    is genuine mathematics.  Decision and the pending universal gate
    `IUT-I.definition-3.1-A2-arithmetic-to-source-gate`
    (SourceDefinition31Quantifiers.lean:1770) are recorded in report
    section 18; no Lean bridge is claimed here.

  Dependency directions (at the SHAs recorded in report section 18):
  * SourceDefinition31RootLemmas imports SourceDefinition31Boundary
    (the trace layer sits above the contract); the reverse import does
    not exist.
  * SourceDefinition31Quantifiers imports foundations only; it never
    imports the boundary or the legacy contract (self-declared at
    SourceDefinition31Quantifiers.lean:149).
  * the dual-contract alignment leaf
    (SourceDefinition31DualContractAlignment.lean, HodgeTheater) links
    the legacy contract to the boundary contract at the arithmetic root
    only; the trace bridge below composes with it (Section 3).

  Consumers (current bytes):
  * boundary contract: Theorem311Source.OriginalInput (:41-46),
    H1FamilyPackage (SourceH1H2Construction.lean:273-278),
    SourceHodgeTheaterBridge (:41), SourceRealizationLifting (:46),
    SourceCompletionK1K2Wiring (:57), the D2/D3D4/D5D8 root modules,
    and SourceDefinition31RootLemmas.
  * StageConstructionTrace: SourceDefinition31RootLemmas internal only
    (`toSource` and its field lemmas at :3807-3906); no external module
    consumes it.
  * SourceNativeInitialThetaData: SourceCompletion.lean
    (`toSourceNativeInitialThetaData` :601) and
    SourceClauseConstructors.lean (:1107).

  What is proved here: `SourceDefinition31Data` and
  `StageConstructionTrace` carry the same information
  (`sourceStageConstructionTraceEquiv`, both round trips, and `toSource`
  is a bijection); the trace assembled over the current side of a
  dual-contract alignment carries the legacy-side arithmetic root; and
  the native boundary projects to the same arithmetic root type.

  Not asserted (card `IUT-I.definition31-carrier-consolidation`): any
  equivalence between `SourceNativeInitialThetaData` and the abstract
  contract, in either direction.  The seven minimal repair
  specifications for the cross-contract gaps and the native-versus-
  contract decision paragraph are recorded in
  `D:\lean\logs\coordination\hodge-theater-family-laws-20261016.md`
  section 18.

  Placement: IUTI/HodgeTheater keeps this leaf beside the other
  family-layer consolidation leaves; its imports point downwards into
  IUTI/InitialTheta, and no existing module imports this one.
-/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31DualContractAlignment
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31RootLemmas
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open Theorem311Source
open Theorem311Source.SourceDefinition31Root.Definition31StageKernel

noncomputable section

/-! ## 1. The trace-to-source bridge -/

/-- The section of `StageConstructionTrace.toSource`: fill the redundant
`partition` slot by `reduction.partition`. -/
def stageConstructionTraceOfSource {l : PrimeGeFive}
    (S : SourceDefinition31Data l) : StageConstructionTrace l where
  arithmetic := S.arithmetic
  selectedPlaces := S.selectedPlaces
  badPlaces := S.badPlaces
  partition := S.reduction.partition
  reduction := S.reduction
  partition_alignment := rfl
  torsion := S.torsion
  orbicurve := S.orbicurve
  sections := S.sections
  cusp := S.cusp
  arithmetic_reduction_compatibility :=
    S.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved :=
    S.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility :=
    S.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved :=
    S.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility :=
    S.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved :=
    S.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility :=
    S.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved :=
    S.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility :=
    S.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved :=
    S.arithmetic_cusp_compatibility_proved

@[simp] theorem stageConstructionTraceOfSource_arithmetic {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).arithmetic = S.arithmetic :=
  rfl

@[simp] theorem stageConstructionTraceOfSource_selectedPlaces {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).selectedPlaces = S.selectedPlaces :=
  rfl

@[simp] theorem stageConstructionTraceOfSource_badPlaces {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).badPlaces = S.badPlaces :=
  rfl

@[simp] theorem stageConstructionTraceOfSource_partition {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).partition = S.reduction.partition :=
  rfl

@[simp] theorem stageConstructionTraceOfSource_reduction {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).reduction = S.reduction :=
  rfl

@[simp] theorem stageConstructionTraceOfSource_torsion {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).torsion = S.torsion :=
  rfl

@[simp] theorem stageConstructionTraceOfSource_orbicurve {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).orbicurve = S.orbicurve :=
  rfl

@[simp] theorem stageConstructionTraceOfSource_sections {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).sections = S.sections :=
  rfl

@[simp] theorem stageConstructionTraceOfSource_cusp {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).cusp = S.cusp :=
  rfl

/-! ## 2. The two round trips, injectivity, and the equivalence -/

theorem toSource_stageConstructionTraceOfSource {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    (stageConstructionTraceOfSource S).toSource = S :=
  rfl

theorem stageConstructionTraceOfSource_toSource {l : PrimeGeFive}
    (T : StageConstructionTrace l) :
    stageConstructionTraceOfSource T.toSource = T := by
  cases T with
  | mk arithmetic selectedPlaces badPlaces partition reduction
      partition_alignment torsion orbicurve sections cusp
      arcZ arcZP atZ atZP aoZ aoZP asZ asZP acZ acZP =>
    cases partition_alignment
    rfl

theorem toSource_injective {l : PrimeGeFive} :
    Function.Injective
      (fun T : StageConstructionTrace l => T.toSource) :=
  Function.LeftInverse.injective
    (fun T => stageConstructionTraceOfSource_toSource T)

theorem stageConstructionTraceOfSource_injective {l : PrimeGeFive} :
    Function.Injective
      (stageConstructionTraceOfSource (l := l)) :=
  Function.LeftInverse.injective
    (fun S => toSource_stageConstructionTraceOfSource S)

theorem toSource_bijective {l : PrimeGeFive} :
    Function.Bijective
      (fun T : StageConstructionTrace l => T.toSource) :=
  ⟨toSource_injective, fun S =>
    ⟨stageConstructionTraceOfSource S,
      toSource_stageConstructionTraceOfSource S⟩⟩

/-- The two current-side carriers carry the same information. -/
def sourceStageConstructionTraceEquiv {l : PrimeGeFive} :
    SourceDefinition31Data l ≃ StageConstructionTrace l where
  toFun := stageConstructionTraceOfSource
  invFun := fun T => T.toSource
  left_inv := fun S => toSource_stageConstructionTraceOfSource S
  right_inv := fun T => stageConstructionTraceOfSource_toSource T

/-! ## 3. Root-level relationships across the three carriers -/

/-- The trace assembled from the current side of a dual-contract
alignment carries the legacy-side arithmetic root: the three carriers
meet at the shared root without drift. -/
theorem stageConstructionTrace_of_alignment_arithmetic {l : PrimeGeFive}
    (A : Definition31DualContractAlignment l) :
    (stageConstructionTraceOfSource A.current).arithmetic =
      A.legacy.candidate.arithmetic :=
  (stageConstructionTraceOfSource_arithmetic A.current).trans
    A.arithmetic_agreement_symm

/-- The arithmetic root of the native quantifier-boundary datum, in the
same shape as the two contract projections. -/
def sourceNativeInitialThetaArithmetic {l : PrimeGeFive}
    (T : InitialThetaSource.SourceNativeInitialThetaData l) :
    InitialThetaArithmeticData l :=
  T.arithmetic

theorem sourceNativeInitialThetaArithmetic_spec {l : PrimeGeFive}
    (T : InitialThetaSource.SourceNativeInitialThetaData l) :
    sourceNativeInitialThetaArithmetic T = T.arithmetic :=
  rfl

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def definition31CarrierConsolidation : Obligation :=
  { id := "IUT-I.definition31-carrier-consolidation"
    source :=
      "IUT I, Definition 3.1 (line 3122); carrier comparison of the " ++
        "current-side records"
    status := VerificationStatus.provedKernel
    note :=
      "Contract consolidation for the current side of Definition 3.1. " ++
        "Proved: SourceDefinition31Data and StageConstructionTrace are " ++
        "information-equivalent (section/retraction with rfl-level " ++
        "forward round trip, toSource bijective, the equivalence " ++
        "sourceStageConstructionTraceEquiv); the trace's extra partition " ++
        "slot is forced by partition_alignment. The trace assembled over " ++
        "an alignment's current side carries the legacy-side arithmetic " ++
        "root, and the native boundary projects to the same root type. " ++
        "Not asserted (card): any equivalence between " ++
        "SourceNativeInitialThetaData and the abstract contract; the " ++
        "carriers are foundation objects against abstract types, so a " ++
        "bridge is genuine mathematics (the pending A2 gate), decided in " ++
        "report section 18. Consumers: Theorem311Source.OriginalInput, " ++
        "H1FamilyPackage, SourceHodgeTheaterBridge; dependency SHAs are " ++
        "recorded in the report."
    dependsOn :=
      [ "IUT-I.definition31-contract-alignment",
        "IUT-I.definition-3.1-root-recognition",
        "IUT-I.definition-3.1-A2-quantifier-boundary" ] }

end LeanFormal.IUT.Audit
