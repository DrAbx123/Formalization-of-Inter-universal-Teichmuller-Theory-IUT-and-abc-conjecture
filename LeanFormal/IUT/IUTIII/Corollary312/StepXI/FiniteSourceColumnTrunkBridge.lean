import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns

/-!
# Finite-column to source-choice trunk bridge (API-9, first half)

This file lands the first half of the finite-model identification interface of
the DSH-F reconnaissance report, section API-9 (`REPORT.md:588-598`): the
common combinatorial trunk of the two Q(i)-at-5 finite presentations of the
Theorem 3.11 indeterminacy data, the canonical map between them, and the
common square contract shared by the (IPL) and (SHE) finite squares.

## Original setting and our route

* Paper: IUT III, Theorem 3.11 and Remark 3.11.1; the finite presentation
  here is the Q(i)-at-5 model with the (Ind1)/(Ind2) label actions on
  `finiteLabel l = Fl l.value` and the (Ind3) level coordinate.
* Repo: `ConcreteFiniteStepXI.FiniteColumnIndex l N` (`procession`, `tensor`,
  `level : Fin (N+1)`; `ConcreteFiniteRouteColumns.lean:77-82`) and
  `ConcreteFiniteTheorem311.ProcessionChoice l` (`processionLabel`,
  `tensorLabel`, `upperSemiLevel`; `ConcreteFiniteModel.lean:98-101`) are
  different types; no bridge was registered between them (`REPORT.md`
  section API-9). `SourceProcessionBoundary.concreteInput`
  (`SourceProcessionBoundary.lean:431-462`) instantiates the source boundary
  `Input` at the concrete data with `Choice := ProcessionChoice l`.
* Our route: extract the common trunk as a structure with two instances
  (both proved by reuse of the frozen `rfl`-level laws), land the canonical
  trunk map `(a, b, k) -> (a, b, k.val)`, and unify the two frozen finite
  squares under one contract.

## What is proved here (no placeholders)

* `ColumnTrunk l Index`: the common trunk interface (`procession`, `tensor`,
  `ind1`, `ind2`, five shift/commutation laws); instances `finiteColumnTrunk`
  and `processionChoiceTrunk`.
* `columnToProcessionChoice`: canonical map, with definitional (Ind1)/(Ind2)
  intertwining (`_ind1`, `_ind2`), projection laws, base compatibility, and
  injectivity; `columnToProcessionChoice_characterization` bundles the gate.
* `ColumnSquareData Index vol`: common square contract; conversion maps
  `FiniteIPLSquare.toColumnSquareData` / `FiniteSHESquare.toColumnSquareData`,
  the canonical instances `finiteIPLSquareData` / `finiteSHESquareData`, and
  two nonemptiness witnesses.

## Reduction points (explicit)

R1. Test carrier only: both sides live on the Q(i)-at-5 finite label type
    with bounded level; nothing here identifies the finite model with an
    arbitrary source Hodge theater (DSH-F sections API-8/API-9).
R2. The map forgets the level bound: `level : Fin (N+1)` is sent to
    `upperSemiLevel := level.val`, and there is no inverse (the (Ind3) level
    of `ProcessionChoice` is unbounded). (Ind3) is deliberately not part of
    `ColumnTrunk`.
R3. The square contract keeps exactly the fields of the frozen finite
    squares; it carries no arithmetic content, no hull/volume comparison,
    and no source realization.

## Trap boundary (DSH-F report T7, `REPORT.md:653-658`) - mandatory

The bridge transports only the combinatorial trunk. It must not be re-exported
as "existence of an arbitrary source", as an arithmetic-existence statement,
or as the API-9 source-carrier identification. The open second half of API-9
is registered below as the named card `sourceColumnCarrierIdentification`.

## Consumers (file:line)

* `StepXI/Contract.lean:32-41`: `StepXIContract.ipl`/`she` slots; the survey
  route pins the evidence slots to the common square contract (T1 discipline:
  no trivially closable `Prop`); this file supplies shape-level nonemptiness.
* `StepXI/ContractSourceReduction.lean:212-215` and `:259-272`: the two
  instantiation sites pass `ipl_evidence`/`she_evidence`; the nonemptiness
  witnesses here are finite-shape inputs, not source-realization evidence.
* `StepXI/ConcreteFiniteRouteColumns.lean:534-641`: the squares converted
  and unified here.
-/

namespace LeanFormal.IUT

noncomputable section

namespace ConcreteFiniteStepXI

/-- Common combinatorial trunk of the finite Theorem-3.11 indeterminacy
presentations: two `finiteLabel`-valued coordinates with the (Ind1)/(Ind2)
label-shift actions and the five frozen shift/commutation laws. -/
structure ColumnTrunk (l : PrimeGeFive) (Index : Type*) where
  procession : Index → ConcreteFiniteTheorem311.finiteLabel l
  tensor : Index → ConcreteFiniteTheorem311.finiteLabel l
  ind1 : ConcreteFiniteTheorem311.finiteLabel l → Index → Index
  ind2 : ConcreteFiniteTheorem311.finiteLabel l → Index → Index
  ind1_procession : ∀ (t : ConcreteFiniteTheorem311.finiteLabel l) (x : Index),
    procession (ind1 t x) = t + procession x
  ind1_tensor : ∀ (t : ConcreteFiniteTheorem311.finiteLabel l) (x : Index),
    tensor (ind1 t x) = tensor x
  ind2_procession : ∀ (t : ConcreteFiniteTheorem311.finiteLabel l) (x : Index),
    procession (ind2 t x) = procession x
  ind2_tensor : ∀ (t : ConcreteFiniteTheorem311.finiteLabel l) (x : Index),
    tensor (ind2 t x) = t + tensor x
  ind1_ind2_commute : ∀ (g h : ConcreteFiniteTheorem311.finiteLabel l) (x : Index),
    ind1 g (ind2 h x) = ind2 h (ind1 g x)

/-- The bounded column model as a trunk (laws reused from the frozen module). -/
def finiteColumnTrunk (l : PrimeGeFive) (N : Nat) :
    ColumnTrunk l (FiniteColumnIndex l N) where
  procession := FiniteColumnIndex.procession
  tensor := FiniteColumnIndex.tensor
  ind1 := FiniteColumnIndex.ind1
  ind2 := FiniteColumnIndex.ind2
  ind1_procession := FiniteColumnIndex.ind1_procession
  ind1_tensor := FiniteColumnIndex.ind1_tensor
  ind2_procession := FiniteColumnIndex.ind2_procession
  ind2_tensor := FiniteColumnIndex.ind2_tensor
  ind1_ind2_commute := FiniteColumnIndex.ind1_ind2_commute

/-- The source-side procession choice (the `Choice` type of
`SourceProcessionBoundary.concreteInput`) as a trunk. -/
def processionChoiceTrunk (l : PrimeGeFive) :
    ColumnTrunk l (ConcreteFiniteTheorem311.ProcessionChoice l) where
  procession := ConcreteFiniteTheorem311.ProcessionChoice.processionLabel
  tensor := ConcreteFiniteTheorem311.ProcessionChoice.tensorLabel
  ind1 := ConcreteFiniteTheorem311.ProcessionChoice.ind1Act
  ind2 := ConcreteFiniteTheorem311.ProcessionChoice.ind2Act
  ind1_procession := ConcreteFiniteTheorem311.ProcessionChoice.ind1_processionLabel
  ind1_tensor := ConcreteFiniteTheorem311.ProcessionChoice.ind1_tensorLabel
  ind2_procession := ConcreteFiniteTheorem311.ProcessionChoice.ind2_processionLabel
  ind2_tensor := ConcreteFiniteTheorem311.ProcessionChoice.ind2_tensorLabel
  ind1_ind2_commute := ConcreteFiniteTheorem311.ProcessionChoice.ind1_ind2_commute

/-- Canonical trunk map from the bounded column model to the source-side
procession choice, `(a, b, k) -> (a, b, k.val)`. -/
def columnToProcessionChoice (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    ConcreteFiniteTheorem311.ProcessionChoice l where
  processionLabel := x.procession
  tensorLabel := x.tensor
  upperSemiLevel := x.level.val

@[simp] theorem columnToProcessionChoice_processionLabel (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    (columnToProcessionChoice l N x).processionLabel = x.procession := rfl

@[simp] theorem columnToProcessionChoice_tensorLabel (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    (columnToProcessionChoice l N x).tensorLabel = x.tensor := rfl

@[simp] theorem columnToProcessionChoice_upperSemiLevel (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    (columnToProcessionChoice l N x).upperSemiLevel = x.level.val := rfl

@[simp] theorem columnToProcessionChoice_base (l : PrimeGeFive) (N : Nat) :
    columnToProcessionChoice l N FiniteColumnIndex.base =
      ConcreteFiniteTheorem311.ProcessionChoice.base := rfl

@[simp] theorem columnToProcessionChoice_ind1 (l : PrimeGeFive) (N : Nat)
    (t : ConcreteFiniteTheorem311.finiteLabel l) (x : FiniteColumnIndex l N) :
    columnToProcessionChoice l N (FiniteColumnIndex.ind1 t x) =
      ConcreteFiniteTheorem311.ProcessionChoice.ind1Act t
        (columnToProcessionChoice l N x) := rfl

@[simp] theorem columnToProcessionChoice_ind2 (l : PrimeGeFive) (N : Nat)
    (t : ConcreteFiniteTheorem311.finiteLabel l) (x : FiniteColumnIndex l N) :
    columnToProcessionChoice l N (FiniteColumnIndex.ind2 t x) =
      ConcreteFiniteTheorem311.ProcessionChoice.ind2Act t
        (columnToProcessionChoice l N x) := rfl

theorem columnToProcessionChoice_injective (l : PrimeGeFive) (N : Nat) :
    Function.Injective (columnToProcessionChoice l N) := by
  intro x y h
  obtain ⟨a, b, k⟩ := x
  obtain ⟨a', b', k'⟩ := y
  have hp : a = a' :=
    congrArg ConcreteFiniteTheorem311.ProcessionChoice.processionLabel h
  have ht : b = b' :=
    congrArg ConcreteFiniteTheorem311.ProcessionChoice.tensorLabel h
  have hl : k = k' :=
    Fin.ext (congrArg ConcreteFiniteTheorem311.ProcessionChoice.upperSemiLevel h)
  rw [hp, ht, hl]

/-- Characterization gate for the canonical trunk map: it intertwines both
label actions (definitionally) and is injective. -/
theorem columnToProcessionChoice_characterization (l : PrimeGeFive) (N : Nat) :
    (∀ (t : ConcreteFiniteTheorem311.finiteLabel l) (x : FiniteColumnIndex l N),
        columnToProcessionChoice l N (FiniteColumnIndex.ind1 t x) =
          ConcreteFiniteTheorem311.ProcessionChoice.ind1Act t
            (columnToProcessionChoice l N x)) ∧
      (∀ (t : ConcreteFiniteTheorem311.finiteLabel l) (x : FiniteColumnIndex l N),
        columnToProcessionChoice l N (FiniteColumnIndex.ind2 t x) =
          ConcreteFiniteTheorem311.ProcessionChoice.ind2Act t
            (columnToProcessionChoice l N x)) ∧
      Function.Injective (columnToProcessionChoice l N) :=
  ⟨columnToProcessionChoice_ind1 l N, columnToProcessionChoice_ind2 l N,
    columnToProcessionChoice_injective l N⟩

/-- Common square contract of the finite (IPL)/(SHE) presentations: two
commuting bijections together with two volume-invariance laws. -/
structure ColumnSquareData (Index : Type*) (vol : Index → Real) where
  horizontal : Index ≃ Index
  vertical : Index ≃ Index
  commute : ∀ x, horizontal (vertical x) = vertical (horizontal x)
  horizontal_volume : ∀ x, vol (horizontal x) = vol x
  vertical_volume : ∀ x, vol (vertical x) = vol x

namespace FiniteIPLSquare

/-- Forget the IPL square to the common square contract. -/
def toColumnSquareData {l : PrimeGeFive} {N : Nat} (S : FiniteIPLSquare l N) :
    ColumnSquareData (FiniteColumnIndex l N) (columnLogVolume l) where
  horizontal := S.horizontal
  vertical := S.vertical
  commute := S.commute
  horizontal_volume := S.horizontal_volume
  vertical_volume := S.vertical_volume

end FiniteIPLSquare

namespace FiniteSHESquare

/-- Forget the SHE square to the common square contract. -/
def toColumnSquareData {l : PrimeGeFive} {N : Nat} (S : FiniteSHESquare l N) :
    ColumnSquareData (FiniteColumnIndex l N) (columnLogVolume l) where
  horizontal := S.horizontal
  vertical := S.vertical
  commute := S.commute
  horizontal_volume := S.horizontal_volume
  vertical_volume := S.vertical_volume

end FiniteSHESquare

/-- The canonical IPL square as a common square. -/
def finiteIPLSquareData (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l) :
    ColumnSquareData (FiniteColumnIndex l N) (columnLogVolume l) :=
  (finiteIPLSquare l N g h).toColumnSquareData

/-- The canonical SHE square as a common square. -/
def finiteSHESquareData (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l) :
    ColumnSquareData (FiniteColumnIndex l N) (columnLogVolume l) :=
  (finiteSHESquare l N g).toColumnSquareData

theorem finiteIPLSquareData_nonempty (l : PrimeGeFive) (N : Nat) :
    Nonempty (ColumnSquareData (FiniteColumnIndex l N) (columnLogVolume l)) :=
  ⟨finiteIPLSquareData l N 0 0⟩

theorem finiteSHESquareData_nonempty (l : PrimeGeFive) (N : Nat) :
    Nonempty (ColumnSquareData (FiniteColumnIndex l N) (columnLogVolume l)) :=
  ⟨finiteSHESquareData l N 0⟩

end ConcreteFiniteStepXI

namespace Audit

/-- Landed first half of API-9: the common trunk bridge of the two finite
Q(i)-at-5 presentations, proved on the finite carriers only. -/
def finiteSourceColumnTrunkBridge : Obligation :=
  { id := "IUT-III.finite-source-column-trunk-bridge"
    source :=
      "DSH-F reconnaissance report, section API-9 (finite model and source " ++
        "carrier identification, REPORT.md:588-598); paper: IUT III, " ++
        "Theorem 3.11 / Remark 3.11.1 (finite Q(i)-at-5 model)"
    status := VerificationStatus.testCarrier
    note :=
      "Landed first half of the API-9 bridge, proved on the finite " ++
        "Q(i)-at-5 carriers only: the common ColumnTrunk interface with its " ++
        "two instances (FiniteColumnIndex and ProcessionChoice, all laws " ++
        "reused), the canonical map columnToProcessionChoice with " ++
        "definitional (Ind1)/(Ind2) intertwining, projection/base laws and " ++
        "injectivity, and the common ColumnSquareData square contract with " ++
        "the FiniteIPLSquare/FiniteSHESquare conversions, canonical " ++
        "instances and nonemptiness witnesses. NOT included: any " ++
        "identification with an arbitrary source carrier, the FPrimeStrip " ++
        "interface, the (Ind3) coordinate, arithmetic content, or source " ++
        "existence (DSH-F trap T7, REPORT.md:653-658)."
    dependsOn :=
      [ "IUT-III.concrete-finite-stepXI-route",
        "IUT-III.concrete-finite-theorem311-model" ] }

/-- Named card: second half of API-9, the identification of the bounded finite
column model with the actual source carrier. -/
def sourceColumnCarrierIdentification : Obligation :=
  { id := "IUT-III.source-column-carrier-identification"
    source :=
      "DSH-F reconnaissance report, section API-9 (REPORT.md:588-598); " ++
        "paper: IUT III, Theorem 3.11"
    status := VerificationStatus.pending
    note :=
      "Second half of API-9, still open for the identification proper only: a " ++
        "structure-preserving injective map matching the bounded finite column " ++
        "model with SourceProcessionBoundary.Input.carrier : Carrier Label Choice " ++
        "together with the FPrimeStrip V interface. Landed progress: the " ++
        "constructive trunk realization over an arbitrary source input, with " ++
        "explicit label homomorphism, is proved and registered separately as " ++
        "IUT-III.source-column-realization " ++
        "(SourceColumnCarrierIdentification.lean): (Ind1)/(Ind2)/base/level " ++
        "laws unconditional, the bounded (Ind3) square under x.level.val + n <= N, " ++
        "and the concrete specialization to columnToProcessionChoice on " ++
        "concreteInput (SourceProcessionBoundary.lean:431-462). The boundary-module " ++
        "indeterminacy-evidence sites remain (concreteInput_ind1/ind2/ind3, " ++
        "SourceProcessionBoundary.lean:480-504). What remains open: " ++
        "injectivity/full faithfulness and the label-to-FPrimeStrip-V wiring; not " ++
        "derivable from the Core laws alone (trivial-core counterexample over Unit " ++
        "in SourceColumnCarrierIdentification.lean), and needing the source data " ++
        "tracked by API-8 (theorem-3.11-output / multiradial-algorithm); must not " ++
        "be replaced by the finite nonemptiness witnesses (trap T7)."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output",
        "IUT-III.source-procession-boundary",
        "IUT-III.finite-source-column-trunk-bridge",
        "IUT-III.source-column-realization" ] }

end Audit

end

end LeanFormal.IUT
