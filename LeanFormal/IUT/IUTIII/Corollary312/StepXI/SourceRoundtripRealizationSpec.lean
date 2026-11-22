import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceColumnCarrierIdentification

/-!
# Route-2 roundtrip spec (spec-only) and a second model for the trunk factorization

## Original (paper) thinking

In IUT III, Theorem 3.11 / Remark 3.11.1, the identification of the
source-side column data with the arithmetic (Theta-pilot / log-shell) data
is realized through the Kummer and evaluation constructions: going around
the two-path square (IUT II, Corollary 4.10, (ii); the log-Kummer
correspondence) lets one read the column coordinates back out of the
arithmetic data.

## Our route (reduction) and deviation

In this repository the strip-level roundtrip is frozen as the reduced
records `SourceKummerArrow` / `SourceEvaluationArrow` /
`SourceKummerEvaluationSquare` (card `IUT-III.source-kummer-evaluation-arrows`,
file `Theorem311/SourceKummerEvaluationArrows.lean`), which live over
`FPrimeStrip` and `TimesMuQuotient`.  No map in the tree connects those
types to `Choice` or `FiniteColumnIndex l N`, so the roundtrip cannot be
composed with the column-level readback at the type level; this
non-composability is a standing conclusion (report
`api5-one-column-landing-20261016.md`, section 19.1, route 2), not an
unfinished proof.  This file therefore freezes the *column-level clause
that the roundtrip is supposed to implement* as a named demand interface,
`RoundtripRealizationSpec`, with the assembly theorem
`readback_of_roundtripSpec` ("if supplied, then read out") and the gate
`roundtripSpec_nonempty_iff`.  No supplier is claimed; the audit card
below keeps the obligation at status `interface`, and the total card
`IUT-III.source-column-readback` keeps its status unchanged.

Part 2 adds a second concrete model strictly richer than `concreteInput`:
the componentwise square of the finite procession core (two moving
coordinates) with the diagonal embedding as readout.  It inhabits the
trunk factorization, the readback and the roundtrip spec there, showing
the interface is consistent beyond the one-coordinate case.  Both
satisfiability witnesses are ordinary kernel proofs.

## Consumers (file:line)

* `StepXI/ContractSourceReduction.lean:210-223` / `:259-283` (receiver
  argument positions :212-213 / :270-271), through the (SHE)-landing
  evidence producer; see report section 19.3.
* Cards `IUT-III.source-column-realization` / `IUT-III.source-column-readback`
  in `StepXI/SourceColumnCarrierIdentification.lean` (this spec refines the
  readback interface).
* `StepXI/FiniteSourceColumnTrunkBridge.lean` (injective trunk map consumed
  by both models).
-/

namespace LeanFormal.IUT

noncomputable section

open ConcreteFiniteTheorem311

open ConcreteFiniteStepXI

open SourceColumnRealization

universe u v

namespace SourceRoundtripRealization

/-- Named interface freezing the route-2 (Kummer/log-shell roundtrip)
supply for the column readback.  Spec-only: every field is demanded data,
and no supplier exists in this repository.

Field provenance (Kierkegaard card-D verdict, 2026-10-16): (i) `readback`
is the rho object (source realization line); (ii) `read_after_write` is
the "roundtrip implementation" clause to be defined by a future bridge
spec (read-after-write on the column image); (iii) `base_fiber` is the
origin-fiber clause completing the readback interface shape.

No strip-level field appears: strip data (`FPrimeStrip`,
`TimesMuQuotient`) is type-non-composable with the column level, so no
such field could be consumed by the composition.  By
`roundtripSpec_nonempty_iff` this interface is exactly as strong as
`RealizationReadback`; it adds no strength and hides no supply. -/
structure RoundtripRealizationSpec {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice)
    (φ : finiteLabel l →+ Label) (c₀ : Choice) where
  /-- (i) the readback (rho) object -/
  readback : Choice → FiniteColumnIndex l N
  /-- (ii) the roundtrip implementation clause: read after write is the
  identity on the column image -/
  read_after_write : ∀ x : FiniteColumnIndex l N,
    readback (coreColumnRealization core φ c₀ x) = x
  /-- (iii) the origin-fiber clause -/
  base_fiber : ∀ c : Choice,
    readback c = (FiniteColumnIndex.base : FiniteColumnIndex l N) → c = c₀

/-- Assembly ("if supplied, then read out"): a roundtrip spec yields the
readback predicate, hence injectivity of the realization. -/
theorem readback_of_roundtripSpec {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (spec : RoundtripRealizationSpec (N := N) core φ c₀) :
    RealizationReadback (N := N) core φ c₀ :=
  ⟨spec.readback, spec.read_after_write, spec.base_fiber⟩

/-- Packing direction: an existing readback predicate is exactly a
roundtrip spec. -/
def roundtripSpecOfReadback {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationReadback (N := N) core φ c₀) :
    RoundtripRealizationSpec (N := N) core φ c₀ where
  readback := h.choose
  read_after_write := h.choose_spec.1
  base_fiber := h.choose_spec.2

/-- Gate (characterization): the spec is inhabited exactly when the
readback predicate holds on the same data. -/
theorem roundtripSpec_nonempty_iff {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) :
    Nonempty (RoundtripRealizationSpec (N := N) core φ c₀) ↔
      RealizationReadback (N := N) core φ c₀ :=
  ⟨fun ⟨spec⟩ => readback_of_roundtripSpec core φ c₀ spec,
    fun h => ⟨roundtripSpecOfReadback core φ c₀ h⟩⟩

/-- Satisfiability witness 1: the concrete input inhabits the spec,
through its unconditional readback instance. -/
def concreteInput_roundtripSpec (l : PrimeGeFive) (N : Nat) :
    RoundtripRealizationSpec (N := N)
      (SourceProcessionBoundary.Input.concreteInput l).carrier.core
      (AddMonoidHom.id (finiteLabel l))
      (SourceProcessionBoundary.Input.concreteInput l).carrier.core.base :=
  roundtripSpecOfReadback _ _ _ (concreteInput_readback l N)

end SourceRoundtripRealization

open SourceRoundtripRealization

namespace ProductProcessionCore

/-- Componentwise square of any core: both coordinates move independently
and the level is read from the first coordinate.  Generic construction
(valid for every `Core`); it is used here to build the second finite
model. -/
def productCore {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) :
    MultiradialKernel.Core Label (Choice × Choice) where
  base := (core.base, core.base)
  level := fun c => core.level c.1
  ind1 := fun g c => (core.ind1 g c.1, core.ind1 g c.2)
  ind2 := fun g c => (core.ind2 g c.1, core.ind2 g c.2)
  ind3 := fun n c => (core.ind3 n c.1, core.ind3 n c.2)
  ind1_zero := fun c => Prod.ext (core.ind1_zero c.1) (core.ind1_zero c.2)
  ind1_add := fun g h c =>
    Prod.ext (core.ind1_add g h c.1) (core.ind1_add g h c.2)
  ind1_inverse := fun g c =>
    Prod.ext (core.ind1_inverse g c.1) (core.ind1_inverse g c.2)
  ind2_zero := fun c => Prod.ext (core.ind2_zero c.1) (core.ind2_zero c.2)
  ind2_add := fun g h c =>
    Prod.ext (core.ind2_add g h c.1) (core.ind2_add g h c.2)
  ind2_inverse := fun g c =>
    Prod.ext (core.ind2_inverse g c.1) (core.ind2_inverse g c.2)
  ind3_zero := fun c => Prod.ext (core.ind3_zero c.1) (core.ind3_zero c.2)
  ind3_add := fun m n c =>
    Prod.ext (core.ind3_add m n c.1) (core.ind3_add m n c.2)
  ind1_ind2_commute := fun g h c =>
    Prod.ext (core.ind1_ind2_commute g h c.1) (core.ind1_ind2_commute g h c.2)
  ind1_ind3_commute := fun g n c =>
    Prod.ext (core.ind1_ind3_commute g n c.1) (core.ind1_ind3_commute g n c.2)
  ind2_ind3_commute := fun g n c =>
    Prod.ext (core.ind2_ind3_commute g n c.1) (core.ind2_ind3_commute g n c.2)
  ind1_level := fun g c => core.ind1_level g c.1
  ind2_level := fun g c => core.ind2_level g c.1
  ind3_level := fun n c => core.ind3_level n c.1

/-- The componentwise realization is the pair of the realizations
(definitional). -/
theorem productCore_coreColumnRealization {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (x : FiniteColumnIndex l N) :
    coreColumnRealization (productCore core) φ (c₀, c₀) x =
      (coreColumnRealization core φ c₀ x, coreColumnRealization core φ c₀ x) :=
  rfl

/-- The second finite model: the square of the concrete procession core. -/
def productProcessionCore (l : PrimeGeFive) :
    MultiradialKernel.Core (finiteLabel l)
      (ProcessionChoice l × ProcessionChoice l) :=
  productCore (SourceFiniteMultiradial.core l)

/-- Realization formula for the second model: both coordinates equal the
injective trunk map. -/
theorem productProcessionCore_realization (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    coreColumnRealization (productProcessionCore l)
        (AddMonoidHom.id (finiteLabel l))
        (ProcessionChoice.base, ProcessionChoice.base) x =
      (columnToProcessionChoice l N x, columnToProcessionChoice l N x) := by
  have hce : coreColumnRealization (SourceFiniteMultiradial.core l)
      (AddMonoidHom.id (finiteLabel l)) ProcessionChoice.base x =
      columnToProcessionChoice l N x :=
    congrFun (concreteInput_coreColumnRealization_eq l N) x
  rw [productProcessionCore, productCore_coreColumnRealization]
  exact Prod.ext hce hce

/-- The second model inhabits the trunk factorization: the readout is the
diagonal embedding (injective). -/
theorem productProcessionCore_trunkFactorization (l : PrimeGeFive) (N : Nat) :
    RealizationTrunkFactorization (N := N) (productProcessionCore l)
      (AddMonoidHom.id (finiteLabel l))
      (ProcessionChoice.base, ProcessionChoice.base) :=
  ⟨fun p => (p, p), fun _ _ h => congrArg Prod.fst h, fun x =>
    productProcessionCore_realization l N x⟩

/-- Hence the second model inherits the readback. -/
theorem productProcessionCore_readback (l : PrimeGeFive) (N : Nat) :
    RealizationReadback (N := N) (productProcessionCore l)
      (AddMonoidHom.id (finiteLabel l))
      (ProcessionChoice.base, ProcessionChoice.base) :=
  readback_of_trunkFactorization _ _ _
    (productProcessionCore_trunkFactorization l N)

/-- And it inhabits the roundtrip spec: the interface is satisfiable in a
model strictly richer than `concreteInput`. -/
def productProcessionCore_roundtripSpec (l : PrimeGeFive) (N : Nat) :
    RoundtripRealizationSpec (N := N) (productProcessionCore l)
      (AddMonoidHom.id (finiteLabel l))
      (ProcessionChoice.base, ProcessionChoice.base) :=
  roundtripSpecOfReadback _ _ _ (productProcessionCore_readback l N)

end ProductProcessionCore

namespace Audit

/-- Frozen named interface for the route-2 (Kummer/log-shell roundtrip)
supply of the column readback (spec-only). -/
def sourceRoundtripRealizationSpec : Obligation :=
  { id := "IUT-III.source-roundtrip-realization-spec"
    source :=
      "DSH-F reconnaissance report, section API-9; IUT III, Theorem 3.11 / " ++
        "Remark 3.11.1; IUT II, Corollary 4.10, (ii)"
    status := VerificationStatus.interface
    note :=
      "Spec-only freeze of the route-2 roundtrip clause: the named demand " ++
        "interface RoundtripRealizationSpec (readback rho; read-after-write " ++
        "roundtrip law; origin-fiber clause), with the assembly theorem " ++
        "readback_of_roundtripSpec to RealizationReadback and the gate " ++
        "roundtripSpec_nonempty_iff (exactly as strong as the readback " ++
        "predicate). No supplier is constructed; the two missing items " ++
        "recorded by the Kierkegaard card-D verdict (2026-10-16) are (i) the " ++
        "rho object itself (source realization line) and (ii) the roundtrip " ++
        "implementation clause, to be defined by a future bridge spec. " ++
        "Strip-level data stays type-non-composable with the column level " ++
        "(standing conclusion); no strip field appears in the spec. The " ++
        "total card IUT-III.source-column-readback keeps status interface. " ++
        "Satisfiability witnesses (both proved, ordinary kernel): " ++
        "concreteInput_roundtripSpec and productProcessionCore_roundtripSpec."
    dependsOn :=
      [ "IUT-III.source-column-readback",
        "IUT-III.finite-source-column-trunk-bridge" ] }

end Audit

end

end LeanFormal.IUT
