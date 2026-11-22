import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteSourceColumnTrunkBridge
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind1Reduction

/-!
# Source column realization over an arbitrary input (API-9, second half, constructive part)

This file lands the constructive (trunk-realization) half of the API-9
second-half obligation `IUT-III.source-column-carrier-identification` for an
arbitrary source input: a canonical family of "column" elements of any
`MultiradialKernel.Core`, labelled by `ConcreteFiniteStepXI.FiniteColumnIndex l N`,
together with its structure laws and the explicit treatment of the level bound
and of the FPrimeStrip side.

## Frozen statement (coordination report `api5-one-column-landing-20261016.md`, section 17.1)

* Objects: the bounded column model `FiniteColumnIndex l N` over
  `finiteLabel l = Fl l.value = ZMod l.value`; an arbitrary
  `input : SourceProcessionBoundary.Input` with its `Carrier Label Choice`
  (six fields; `ParametricCarrier.lean:25-33`), its `Core Label Choice`
  (nineteen fields; `MultiradialOutputKernel.lean:12-31`), and its theater
  data including `primeStrip : FPrimeStrip V` (`HodgeTheaterCore.lean:31-34`).
* Extra identification data: a label homomorphism
  `φ : finiteLabel l →+ Label` (no canonical choice exists in general, hence
  an explicit hypothesis) and the base point `carrier.core.base`.
* Conclusion, per point `x : FiniteColumnIndex l N`: the realization
  `ind1 (φ x.procession) (ind2 (φ x.tensor) (ind3 x.level.val base))`
  (i) intertwines (Ind1) and (Ind2) unconditionally; (ii) has the level
  formula `level (realization x) = level base + x.level.val`; (iii) satisfies
  the (Ind3) square exactly under the side condition `x.level.val + n ≤ N`;
  (iv) specializes to `columnToProcessionChoice` on `concreteInput`.
* NOT in the conclusion (parked; sharpness examples below):
  unconditional injectivity/surjectivity ("identification proper"), the
  label-level interface to the FPrimeStrip `V`, and any source existence
  (trap T7 of the DSH-F report, `REPORT.md:653-658`). The *conditional*
  injectivity statement is proved below (section "Readback"): the canonical
  realization is injective under the readback hypothesis, which is provably
  the weakest one on the same data (see R5); the
  unconditional finite instance on `concreteInput` is recorded in R6.

## Reduction points (explicit)

R1. The realization consumes only `Input.carrier.core`; the theater, history,
    packet-volume, target-q and route-normal-form fields, and the
    `FPrimeStrip V` data, are not consumed. The construction is uniform in the
    source input.
R2. The label homomorphism φ is an explicit parameter. For the concrete
    Q(i)-at-5 input, φ is the identity; for an arbitrary input neither φ nor
    its injectivity is manufactured.
R2b. The (Ind1)/(Ind2) squares compare the core shift by `φ t` with a
    realization whose labels are `φ x.procession` / `φ x.tensor`; the needed
    commutation of the two transported labels is discharged from commutativity
    of the label domain (`finiteLabel l = ZMod l.value`), so `Label` itself is
    only assumed to be an additive group. The helper lemmas carry the
    commutation explicitly: `core_ind1_rotate_of_comm`,
    `core_ind2_rotate_of_comm`.
R3. The (Ind3) law carries the explicit side condition `x.level.val + n ≤ N`;
    the truncation obstruction below shows it is not removable for the
    canonical map. All other laws are unconditional: there the level bound is
    provably unnecessary.
R4. Unconditional injectivity is not claimed: the trivial-action core over
    `Unit` satisfies every `Core` law, while no map into `Unit` is injective
    (`trivialCore_no_injective_phi`: the failure holds for *every* label map
    φ, injective or not). The identification proper needs the actual
    faithfulness of the source actions (API-8 data) and the FPrimeStrip
    interface, which remain open.
R5. Conditional injectivity: on the same data, injectivity of the realization
    is *equivalent* to the existence of a readback / left inverse
    (`leftInverse_iff_injective`; `readback_of_leftInverse`), so the readback
    hypothesis is the weakest additional predicate that yields injectivity;
    its origin-fiber clause (`ρ c = base → c = c₀`) is provably free of
    extra strength. This is a *technical minimalization* predicate; its
    paper dictionary (finite-model shadow of the output-faithfulness content
    of IUT III, Theorem 3.11 / Remark 3.11.1) is a candidate to be confirmed
    by the paper owner.

R6. Finite instance (follow-up evaluation, 2026-10-16): for the concrete
    input `Input.concreteInput l` the realization is exactly the injective
    trunk map `columnToProcessionChoice`, so injectivity, the left inverse
    and `RealizationReadback` hold there *unconditionally* for every `l`,
    `N` (`concreteInput_readback`); the general-input statement remains the
    conditional card `IUT-III.source-column-readback`.  The conditional
    supply shape landed alongside is `RealizationTrunkFactorization`
    (faithful finite-trunk readout through an injective `j`), which implies
    the readback; the strip-level Kummer/evaluation roundtrip interfaces are
    not type-composable with it (no strip-to-`Choice` dictionary; that is
    the forwarded FPrimeStrip wiring request).

## Consumers (file:line)

* `StepXI/FiniteSourceColumnTrunkBridge.lean` (canonical map specialized to
  here; card `IUT-III.source-column-carrier-identification` notes updated).
* `StepXI/ContractSourceReduction.lean:212-215` / `:259-272` (shape-level
  evidence sites; unchanged, cited only).
* `Corollary312/Obligations.lean:5-24` (`IUT-III.IPL/SHE/APT` chain; the
  realization is the source-side column input for future slot assembly).
-/

namespace LeanFormal.IUT

open ConcreteFiniteTheorem311

open ConcreteFiniteStepXI

noncomputable section

namespace SourceColumnRealization

universe u v uv

/-- Rotation of two (Ind1) shifts, under the commutativity hypothesis for the
two labels involved only; the ambient group is a general additive group. -/
theorem core_ind1_rotate_of_comm {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) {a b : Label}
    (h : b + a = a + b) (c : Choice) :
    core.ind1 a (core.ind1 b c) = core.ind1 b (core.ind1 a c) :=
  calc core.ind1 a (core.ind1 b c) = core.ind1 (b + a) c :=
        (core.ind1_add b a c).symm
    _ = core.ind1 (a + b) c := by rw [h]
    _ = core.ind1 b (core.ind1 a c) := core.ind1_add a b c

/-- Rotation of two (Ind2) shifts, under the commutativity hypothesis for the
two labels involved only; the ambient group is a general additive group. -/
theorem core_ind2_rotate_of_comm {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) {a b : Label}
    (h : b + a = a + b) (c : Choice) :
    core.ind2 a (core.ind2 b c) = core.ind2 b (core.ind2 a c) :=
  calc core.ind2 a (core.ind2 b c) = core.ind2 (b + a) c :=
        (core.ind2_add b a c).symm
    _ = core.ind2 (a + b) c := by rw [h]
    _ = core.ind2 b (core.ind2 a c) := core.ind2_add a b c

/-- The canonical column realization over any core: labels are transported by
the homomorphism φ and the level coordinate is applied via (Ind3). -/
def coreColumnRealization {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice)
    (φ : finiteLabel l →+ Label) (c₀ : Choice)
    (x : FiniteColumnIndex l N) : Choice :=
  core.ind1 (φ x.procession) (core.ind2 (φ x.tensor) (core.ind3 x.level.val c₀))

/-- (Ind1) intertwining of the realization (unconditional). -/
theorem coreColumnRealization_ind1 {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (t : finiteLabel l) (x : FiniteColumnIndex l N) :
    coreColumnRealization core φ c₀ (FiniteColumnIndex.ind1 t x) =
      core.ind1 (φ t) (coreColumnRealization core φ c₀ x) := by
  unfold coreColumnRealization
  simp only [FiniteColumnIndex.ind1_procession, FiniteColumnIndex.ind1_tensor,
    FiniteColumnIndex.ind1_level]
  rw [map_add, core.ind1_add]
  have hcomm : φ t + φ x.procession = φ x.procession + φ t :=
    calc φ t + φ x.procession = φ (t + x.procession) :=
          (map_add φ t x.procession).symm
      _ = φ (x.procession + t) := congrArg φ (add_comm t x.procession)
      _ = φ x.procession + φ t := map_add φ x.procession t
  exact core_ind1_rotate_of_comm core hcomm
    (core.ind2 (φ x.tensor) (core.ind3 x.level.val c₀))

/-- (Ind2) intertwining of the realization (unconditional). -/
theorem coreColumnRealization_ind2 {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (t : finiteLabel l) (x : FiniteColumnIndex l N) :
    coreColumnRealization core φ c₀ (FiniteColumnIndex.ind2 t x) =
      core.ind2 (φ t) (coreColumnRealization core φ c₀ x) := by
  unfold coreColumnRealization
  simp only [FiniteColumnIndex.ind2_procession, FiniteColumnIndex.ind2_tensor,
    FiniteColumnIndex.ind2_level]
  rw [map_add, core.ind2_add]
  have hcomm : φ x.tensor + φ t = φ t + φ x.tensor :=
    calc φ x.tensor + φ t = φ (x.tensor + t) :=
          (map_add φ x.tensor t).symm
      _ = φ (t + x.tensor) := congrArg φ (add_comm x.tensor t)
      _ = φ t + φ x.tensor := map_add φ t x.tensor
  calc core.ind1 (φ x.procession)
        (core.ind2 (φ x.tensor) (core.ind2 (φ t) (core.ind3 x.level.val c₀)))
      = core.ind1 (φ x.procession)
        (core.ind2 (φ t) (core.ind2 (φ x.tensor) (core.ind3 x.level.val c₀))) :=
        congrArg (fun y => core.ind1 (φ x.procession) y)
          (core_ind2_rotate_of_comm core hcomm (core.ind3 x.level.val c₀)).symm
    _ = core.ind2 (φ t)
        (core.ind1 (φ x.procession)
          (core.ind2 (φ x.tensor) (core.ind3 x.level.val c₀))) :=
        core.ind1_ind2_commute (φ x.procession) (φ t)
          (core.ind2 (φ x.tensor) (core.ind3 x.level.val c₀))

/-- (Ind3) intertwining of the realization, exactly under the side condition
that the level coordinate is not truncated. -/
theorem coreColumnRealization_ind3 {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (n : Nat) (x : FiniteColumnIndex l N)
    (h : x.level.val + n ≤ N) :
    coreColumnRealization core φ c₀ (FiniteColumnIndex.ind3 n x) =
      core.ind3 n (coreColumnRealization core φ c₀ x) := by
  have hlevel : (FiniteColumnIndex.ind3 n x).level.val = x.level.val + n := by
    rw [FiniteColumnIndex.ind3_level_val, Nat.min_eq_right h]
  unfold coreColumnRealization
  simp only [FiniteColumnIndex.ind3_procession, FiniteColumnIndex.ind3_tensor,
    hlevel]
  rw [core.ind3_add]
  calc core.ind1 (φ x.procession)
        (core.ind2 (φ x.tensor) (core.ind3 n (core.ind3 x.level.val c₀)))
      = core.ind1 (φ x.procession)
        (core.ind3 n (core.ind2 (φ x.tensor) (core.ind3 x.level.val c₀))) :=
        congrArg (fun y => core.ind1 (φ x.procession) y)
          (core.ind2_ind3_commute (φ x.tensor) n (core.ind3 x.level.val c₀))
    _ = core.ind3 n
        (core.ind1 (φ x.procession)
          (core.ind2 (φ x.tensor) (core.ind3 x.level.val c₀))) :=
        core.ind1_ind3_commute (φ x.procession) n
          (core.ind2 (φ x.tensor) (core.ind3 x.level.val c₀))

/-- The (Ind3) square is unconditional for `n = 0`. -/
theorem coreColumnRealization_ind3_zero {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (x : FiniteColumnIndex l N) :
    coreColumnRealization core φ c₀ (FiniteColumnIndex.ind3 0 x) =
      coreColumnRealization core φ c₀ x := by
  rw [FiniteColumnIndex.ind3_zero]

/-- The realization sends the column base to the chosen base point. -/
theorem coreColumnRealization_base {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) :
    coreColumnRealization core φ c₀ (FiniteColumnIndex.base : FiniteColumnIndex l N) =
      c₀ := by
  unfold coreColumnRealization
  simp only [FiniteColumnIndex.base_procession, FiniteColumnIndex.base_tensor,
    FiniteColumnIndex.base_level, Fin.val_zero]
  rw [map_zero, core.ind3_zero, core.ind2_zero, core.ind1_zero]

/-- Level formula for the realization (uses the carrier's exact (Ind3) level
law, which is not part of `Core`). -/
theorem carrier_coreColumnRealization_level {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (φ : finiteLabel l →+ Label) (c₀ : Choice) (x : FiniteColumnIndex l N) :
    carrier.core.level (coreColumnRealization carrier.core φ c₀ x) =
      carrier.core.level c₀ + x.level.val := by
  unfold coreColumnRealization
  rw [carrier.core.ind1_level, carrier.core.ind2_level, carrier.ind3_level_eq]

/-- The column realization over a source input, with base point the carrier
core base (`Input.baseChoice` is equal to it by the input field). -/
def inputColumnRealization {l : PrimeGeFive}
    {V : Type uv} {Label : Type u} {Choice : Type v} [AddGroup Label]
    (input : SourceProcessionBoundary.Input (l := l) (V := V)
      (Label := Label) (Choice := Choice))
    (φ : finiteLabel l →+ Label) (N : Nat)
    (x : FiniteColumnIndex l N) : Choice :=
  coreColumnRealization input.carrier.core φ input.carrier.core.base x

/-- (Ind1) intertwining over the source input. -/
theorem inputColumnRealization_ind1 {l : PrimeGeFive}
    {V : Type uv} {Label : Type u} {Choice : Type v} [AddGroup Label]
    (input : SourceProcessionBoundary.Input (l := l) (V := V)
      (Label := Label) (Choice := Choice))
    (φ : finiteLabel l →+ Label) (N : Nat) (t : finiteLabel l)
    (x : FiniteColumnIndex l N) :
    inputColumnRealization input φ N (FiniteColumnIndex.ind1 t x) =
      input.carrier.core.ind1 (φ t) (inputColumnRealization input φ N x) := by
  unfold inputColumnRealization
  exact coreColumnRealization_ind1 input.carrier.core φ input.carrier.core.base t x

/-- (Ind2) intertwining over the source input. -/
theorem inputColumnRealization_ind2 {l : PrimeGeFive}
    {V : Type uv} {Label : Type u} {Choice : Type v} [AddGroup Label]
    (input : SourceProcessionBoundary.Input (l := l) (V := V)
      (Label := Label) (Choice := Choice))
    (φ : finiteLabel l →+ Label) (N : Nat) (t : finiteLabel l)
    (x : FiniteColumnIndex l N) :
    inputColumnRealization input φ N (FiniteColumnIndex.ind2 t x) =
      input.carrier.core.ind2 (φ t) (inputColumnRealization input φ N x) := by
  unfold inputColumnRealization
  exact coreColumnRealization_ind2 input.carrier.core φ input.carrier.core.base t x

/-- (Ind3) intertwining over the source input, under the untruncated side
condition. -/
theorem inputColumnRealization_ind3 {l : PrimeGeFive}
    {V : Type uv} {Label : Type u} {Choice : Type v} [AddGroup Label]
    (input : SourceProcessionBoundary.Input (l := l) (V := V)
      (Label := Label) (Choice := Choice))
    (φ : finiteLabel l →+ Label) (N : Nat) (n : Nat) (x : FiniteColumnIndex l N)
    (h : x.level.val + n ≤ N) :
    inputColumnRealization input φ N (FiniteColumnIndex.ind3 n x) =
      input.carrier.core.ind3 n (inputColumnRealization input φ N x) := by
  unfold inputColumnRealization
  exact coreColumnRealization_ind3 input.carrier.core φ input.carrier.core.base n x h

/-- Base law over the source input. -/
theorem inputColumnRealization_base {l : PrimeGeFive}
    {V : Type uv} {Label : Type u} {Choice : Type v} [AddGroup Label]
    (input : SourceProcessionBoundary.Input (l := l) (V := V)
      (Label := Label) (Choice := Choice))
    (φ : finiteLabel l →+ Label) (N : Nat) :
    inputColumnRealization input φ N (FiniteColumnIndex.base : FiniteColumnIndex l N) =
      input.carrier.core.base := by
  unfold inputColumnRealization
  exact coreColumnRealization_base input.carrier.core φ input.carrier.core.base

/-- Level formula over the source input. -/
theorem inputColumnRealization_level {l : PrimeGeFive}
    {V : Type uv} {Label : Type u} {Choice : Type v} [AddGroup Label]
    (input : SourceProcessionBoundary.Input (l := l) (V := V)
      (Label := Label) (Choice := Choice))
    (φ : finiteLabel l →+ Label) (N : Nat) (x : FiniteColumnIndex l N) :
    input.carrier.core.level (inputColumnRealization input φ N x) =
      input.carrier.core.level input.carrier.core.base + x.level.val := by
  unfold inputColumnRealization
  exact carrier_coreColumnRealization_level input.carrier φ input.carrier.core.base x

/-- Concrete specialization: on the Q(i)-at-5 input with identity labels, the
realization is the canonical bridge map `columnToProcessionChoice`. -/
theorem concreteInput_inputColumnRealization_eq (l : PrimeGeFive) (N : Nat) :
    inputColumnRealization (SourceProcessionBoundary.Input.concreteInput l)
        (AddMonoidHom.id (finiteLabel l)) N =
      columnToProcessionChoice l N := by
  funext x
  change coreColumnRealization (SourceFiniteMultiradial.core l)
      (AddMonoidHom.id (finiteLabel l)) ProcessionChoice.base x =
    columnToProcessionChoice l N x
  simp only [coreColumnRealization, SourceFiniteMultiradial.core,
    columnToProcessionChoice, AddMonoidHom.id_apply,
    ProcessionChoice.ind1Act, ProcessionChoice.ind2Act, ProcessionChoice.ind3Lift,
    ProcessionChoice.base_processionLabel, ProcessionChoice.base_tensorLabel,
    ProcessionChoice.base_upperSemiLevel, add_zero, zero_add]

/-- The trivial (constant-action) core over `Unit`: every `Core` law holds
while `Choice` is a subsingleton. -/
def trivialCore (Label : Type u) [AddGroup Label] :
    MultiradialKernel.Core Label Unit where
  base := ()
  level := fun _ => 0
  ind1 := fun _ c => c
  ind2 := fun _ c => c
  ind3 := fun _ c => c
  ind1_zero := fun _ => rfl
  ind1_add := fun _ _ _ => rfl
  ind1_inverse := fun _ _ => rfl
  ind2_zero := fun _ => rfl
  ind2_add := fun _ _ _ => rfl
  ind2_inverse := fun _ _ => rfl
  ind3_zero := fun _ => rfl
  ind3_add := fun _ _ _ => rfl
  ind1_ind2_commute := fun _ _ _ => rfl
  ind1_ind3_commute := fun _ _ _ => rfl
  ind2_ind3_commute := fun _ _ _ => rfl
  ind1_level := fun _ _ => rfl
  ind2_level := fun _ _ => rfl
  ind3_level := fun _ _ => Nat.zero_le 0

/-- On the trivial core the realization is constant. -/
theorem trivialCore_coreColumnRealization {l : PrimeGeFive} {N : Nat}
    {Label : Type u} [AddGroup Label] (φ : finiteLabel l →+ Label)
    (x : FiniteColumnIndex l N) :
    coreColumnRealization (trivialCore Label) φ () x = () := rfl

/-- Sharpness: no injectivity can be claimed from the `Core` laws alone. The
realization over the trivial core is constant, and two distinct columns (the
base and its (Ind3)-translate at `N = 1`) have the same image. -/
theorem trivialCore_coreColumnRealization_not_injective (l : PrimeGeFive) :
    ¬ Function.Injective
      (coreColumnRealization (trivialCore (finiteLabel l))
        (AddMonoidHom.id (finiteLabel l)) () (N := 1)) := by
  intro hinj
  have hconst :
      coreColumnRealization (trivialCore (finiteLabel l))
          (AddMonoidHom.id (finiteLabel l)) () (N := 1)
          (FiniteColumnIndex.base : FiniteColumnIndex l 1) =
        coreColumnRealization (trivialCore (finiteLabel l))
          (AddMonoidHom.id (finiteLabel l)) () (N := 1)
          (FiniteColumnIndex.ind3 1 (FiniteColumnIndex.base : FiniteColumnIndex l 1)) := by
    simp [coreColumnRealization, trivialCore]
  have h := hinj hconst
  have hlevel := congrArg (fun x : FiniteColumnIndex l 1 => x.level.val) h
  simp only [FiniteColumnIndex.base_level, FiniteColumnIndex.ind3_level_val,
    Fin.val_zero, zero_add, Nat.min_self] at hlevel
  omega

/-- Sharpness of the (Ind3) side condition: for the canonical map the
unbounded (Ind3) square already fails at `N = 1` (the target level is not
truncated while the column side passes through `min N`). -/
theorem columnToProcessionChoice_ind3_truncation_obstruction (l : PrimeGeFive) :
    ProcessionChoice.ind3Lift 1
        (columnToProcessionChoice l 1
          (FiniteColumnIndex.ind3 1 (FiniteColumnIndex.base : FiniteColumnIndex l 1))) ≠
      columnToProcessionChoice l 1
        (FiniteColumnIndex.ind3 1
          (FiniteColumnIndex.ind3 1 (FiniteColumnIndex.base : FiniteColumnIndex l 1))) := by
  intro h
  have hlevel := congrArg ProcessionChoice.upperSemiLevel h
  simp only [ProcessionChoice.ind3_upperSemiLevel,
    columnToProcessionChoice_upperSemiLevel, FiniteColumnIndex.ind3_level_val,
    FiniteColumnIndex.base_level, Fin.val_zero, zero_add, Nat.min_self] at hlevel
  omega

/-! ## Readback: the weakest additional hypothesis for injectivity

`trivialCore_no_injective_phi` below shows that no hypothesis on the label
map alone can repair injectivity: the trivial-action core fails for *every*
φ. The weakest hypothesis on the full data `(core, φ, c₀)` is injectivity
itself; the lemmas below show that the existence of a readback (left
inverse) is *equivalent* to it, and package the readback in the source-side
shape used for the identification interface ("read back to the base column
implies the point is the base point"). -/

/-- The weakest realization-side hypothesis: an explicit left inverse
("readback") for the canonical realization `coreColumnRealization core φ c₀`.
By `leftInverse_iff_injective` this is *equivalent* to injectivity of the
realization, so it is exactly as weak as the conclusion it is used to
derive. Technical minimalization predicate; paper candidate = the
finite-model shadow of the output-faithfulness content of IUT III,
Theorem 3.11 / Remark 3.11.1, to be confirmed by the paper owner. -/
def RealizationLeftInverse {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice)
    (φ : finiteLabel l →+ Label) (c₀ : Choice) : Prop :=
  ∃ ρ : Choice → FiniteColumnIndex l N,
    ∀ x : FiniteColumnIndex l N, ρ (coreColumnRealization core φ c₀ x) = x

/-- Source-interface form of the left inverse: a readback `ρ` together with
the origin-fiber clause (`ρ c = base` forces `c = c₀`), matching the shape
of a source-side readback through the Kummer / log-shell context. The clause
adds no strength (`readback_of_leftInverse`), so this predicate is
equivalent to injectivity as well. -/
def RealizationReadback {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice)
    (φ : finiteLabel l →+ Label) (c₀ : Choice) : Prop :=
  ∃ ρ : Choice → FiniteColumnIndex l N,
    (∀ x : FiniteColumnIndex l N, ρ (coreColumnRealization core φ c₀ x) = x) ∧
    (∀ c : Choice, ρ c = (FiniteColumnIndex.base : FiniteColumnIndex l N) → c = c₀)

/-- A left inverse yields injectivity of the realization. -/
theorem coreColumnRealization_injective_of_leftInverse {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationLeftInverse (N := N) core φ c₀) :
    Function.Injective (coreColumnRealization (N := N) core φ c₀) := by
  intro x y hxy
  calc x = h.choose (coreColumnRealization core φ c₀ x) := (h.choose_spec x).symm
    _ = h.choose (coreColumnRealization core φ c₀ y) := by rw [hxy]
    _ = y := h.choose_spec y

/-- Conversely, injectivity yields an explicit left inverse (classical
choice); together with the previous theorem this shows that no readback
hypothesis can be weakened while still implying injectivity. -/
theorem leftInverse_of_injective {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice)
    (h : Function.Injective (coreColumnRealization (N := N) core φ c₀)) :
    RealizationLeftInverse (N := N) core φ c₀ := by
  classical
  refine ⟨fun c =>
    if hex : ∃ x : FiniteColumnIndex l N, coreColumnRealization core φ c₀ x = c
      then hex.choose else FiniteColumnIndex.base, fun x => ?_⟩
  have hx : ∃ y : FiniteColumnIndex l N,
      coreColumnRealization core φ c₀ y = coreColumnRealization core φ c₀ x :=
    ⟨x, rfl⟩
  change (if hex : ∃ y : FiniteColumnIndex l N,
      coreColumnRealization core φ c₀ y = coreColumnRealization core φ c₀ x
      then hex.choose else FiniteColumnIndex.base) = x
  exact (dif_pos hx).trans (h hx.choose_spec)

/-- The weakest-hypothesis criterion: on the same data, the existence of a
readback / left inverse and injectivity of the realization are equivalent
predicates, so the readback hypothesis is exactly as strong as the
identification conclusion. -/
theorem leftInverse_iff_injective {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) :
    RealizationLeftInverse (N := N) core φ c₀ ↔
      Function.Injective (coreColumnRealization (N := N) core φ c₀) :=
  ⟨coreColumnRealization_injective_of_leftInverse (N := N) core φ c₀,
    leftInverse_of_injective (N := N) core φ c₀⟩

/-- From a left inverse alone: the origin fiber of the realization is exact
(the realization lands in the base point only at the base column). -/
theorem leftInverse_fiber_base {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationLeftInverse (N := N) core φ c₀)
    {x : FiniteColumnIndex l N} (hx : coreColumnRealization core φ c₀ x = c₀) :
    x = (FiniteColumnIndex.base : FiniteColumnIndex l N) := by
  have hbase : h.choose c₀ = (FiniteColumnIndex.base : FiniteColumnIndex l N) := by
    have hb := h.choose_spec (FiniteColumnIndex.base : FiniteColumnIndex l N)
    rwa [coreColumnRealization_base core φ c₀] at hb
  calc x = h.choose (coreColumnRealization core φ c₀ x) := (h.choose_spec x).symm
    _ = h.choose c₀ := by rw [hx]
    _ = FiniteColumnIndex.base := hbase

/-- Reflection of the readback predicate into a left inverse. -/
theorem readback_to_leftInverse {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationReadback (N := N) core φ c₀) :
    RealizationLeftInverse (N := N) core φ c₀ :=
  ⟨h.choose, h.choose_spec.1⟩

/-- The readback evaluates on realizations. -/
theorem readback_apply {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationReadback (N := N) core φ c₀)
    (x : FiniteColumnIndex l N) :
    h.choose (coreColumnRealization core φ c₀ x) = x :=
  h.choose_spec.1 x

/-- The readback sends the base point to the base column. -/
theorem readback_base {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationReadback (N := N) core φ c₀) :
    h.choose c₀ = (FiniteColumnIndex.base : FiniteColumnIndex l N) := by
  have hb := h.choose_spec.1 (FiniteColumnIndex.base : FiniteColumnIndex l N)
  rwa [coreColumnRealization_base core φ c₀] at hb

/-- Conditional injectivity: the readback hypothesis implies injectivity of
the realization. -/
theorem coreColumnRealization_injective_of_readback {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationReadback (N := N) core φ c₀) :
    Function.Injective (coreColumnRealization (N := N) core φ c₀) :=
  coreColumnRealization_injective_of_leftInverse (N := N) core φ c₀
    (readback_to_leftInverse (N := N) core φ c₀ h)

/-- Origin-fiber exactness for the readback package. -/
theorem readback_fiber_base {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationReadback (N := N) core φ c₀)
    {x : FiniteColumnIndex l N} (hx : coreColumnRealization core φ c₀ x = c₀) :
    x = (FiniteColumnIndex.base : FiniteColumnIndex l N) := by
  have h2 : h.choose (coreColumnRealization core φ c₀ x) = h.choose c₀ :=
    congrArg h.choose hx
  rw [readback_apply core φ c₀ h x, readback_base core φ c₀ h] at h2
  exact h2

/-- The readback commutes with the (Ind1) steps of the realization. -/
theorem readback_ind1 {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationReadback (N := N) core φ c₀)
    (t : finiteLabel l) (x : FiniteColumnIndex l N) :
    h.choose (core.ind1 (φ t) (coreColumnRealization core φ c₀ x)) =
      FiniteColumnIndex.ind1 t x := by
  rw [← coreColumnRealization_ind1 core φ c₀ t x]
  exact readback_apply core φ c₀ h (FiniteColumnIndex.ind1 t x)

/-- The readback commutes with the (Ind2) steps of the realization. -/
theorem readback_ind2 {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationReadback (N := N) core φ c₀)
    (t : finiteLabel l) (x : FiniteColumnIndex l N) :
    h.choose (core.ind2 (φ t) (coreColumnRealization core φ c₀ x)) =
      FiniteColumnIndex.ind2 t x := by
  rw [← coreColumnRealization_ind2 core φ c₀ t x]
  exact readback_apply core φ c₀ h (FiniteColumnIndex.ind2 t x)

/-- The readback commutes with the (bounded) (Ind3) steps of the
realization. -/
theorem readback_ind3 {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationReadback (N := N) core φ c₀)
    (n : Nat) (x : FiniteColumnIndex l N) (hN : x.level.val + n ≤ N) :
    h.choose (core.ind3 n (coreColumnRealization core φ c₀ x)) =
      FiniteColumnIndex.ind3 n x := by
  rw [← coreColumnRealization_ind3 core φ c₀ n x hN]
  exact readback_apply core φ c₀ h (FiniteColumnIndex.ind3 n x)

/-- Non-degeneracy of the column carrier: the column obtained from the base
column by a unit (Ind1) shift differs from the base column. The finite label
`ZMod l.value` is nontrivial (`finiteLabel_one_ne_zero`), so this holds for
every `l`, `N`. -/
theorem finiteColumnIndex_ind1_one_ne_base (l : PrimeGeFive) (N : Nat) :
    (FiniteColumnIndex.ind1 1 (FiniteColumnIndex.base : FiniteColumnIndex l N)) ≠
      (FiniteColumnIndex.base : FiniteColumnIndex l N) := by
  intro h
  have h' : (1 : finiteLabel l) = 0 := by
    have h1 := congrArg FiniteColumnIndex.procession h
    simpa only [FiniteColumnIndex.ind1_procession, FiniteColumnIndex.base_procession,
      add_zero] using h1
  exact SourceFiniteMultiradial.finiteLabel_one_ne_zero l h'

/-- The origin-fiber clause of `RealizationReadback` adds no strength: given
a left inverse, it can always be arranged by redirecting outside the image of
the realization (a non-base column exists for every `l`, `N`). Hence
`RealizationReadback` and `RealizationLeftInverse` are equivalent, and both
are equivalent to injectivity of the realization. -/
theorem readback_of_leftInverse {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationLeftInverse (N := N) core φ c₀) :
    RealizationReadback (N := N) core φ c₀ := by
  classical
  refine ⟨fun c =>
    if c = c₀ then (FiniteColumnIndex.base : FiniteColumnIndex l N)
    else if h.choose c = (FiniteColumnIndex.base : FiniteColumnIndex l N)
      then FiniteColumnIndex.ind1 1 (FiniteColumnIndex.base : FiniteColumnIndex l N)
      else h.choose c, ?_, ?_⟩
  · intro x
    dsimp
    by_cases hx : coreColumnRealization core φ c₀ x = c₀
    · rw [if_pos hx]
      exact (leftInverse_fiber_base core φ c₀ h hx).symm
    · rw [if_neg hx]
      by_cases hb : h.choose (coreColumnRealization core φ c₀ x) =
          FiniteColumnIndex.base
      · rw [if_pos hb]
        exfalso
        have hxb : x = (FiniteColumnIndex.base : FiniteColumnIndex l N) :=
          (h.choose_spec x).symm.trans hb
        exact hx (by rw [hxb]; exact coreColumnRealization_base core φ c₀)
      · rw [if_neg hb]
        exact h.choose_spec x
  · intro c hc
    by_cases hc0 : c = c₀
    · exact hc0
    · dsimp at hc
      rw [if_neg hc0] at hc
      by_cases hb : h.choose c = FiniteColumnIndex.base
      · rw [if_pos hb] at hc
        exact absurd hc (finiteColumnIndex_ind1_one_ne_base l N)
      · rw [if_neg hb] at hc
        exact absurd hc hb

/-- Conditional injectivity over the source input. -/
theorem inputColumnRealization_injective_of_readback {l : PrimeGeFive}
    {V : Type uv} {Label : Type u} {Choice : Type v} [AddGroup Label]
    (input : SourceProcessionBoundary.Input (l := l) (V := V)
      (Label := Label) (Choice := Choice))
    (φ : finiteLabel l →+ Label) (N : Nat)
    (h : RealizationReadback (N := N) input.carrier.core φ input.carrier.core.base) :
    Function.Injective (inputColumnRealization input φ N) := by
  unfold inputColumnRealization
  exact coreColumnRealization_injective_of_readback input.carrier.core φ
    input.carrier.core.base h

/-- Sharpness for every label map: whatever φ is (injective or not), the
trivial core over `Unit` has constant realization, so no hypothesis on the
label map alone can repair injectivity. The necessary hypothesis therefore
lies on the `Choice` side (the readback data of `RealizationLeftInverse`). -/
theorem trivialCore_no_injective_phi {l : PrimeGeFive} {Label : Type u}
    [AddGroup Label] (φ : finiteLabel l →+ Label) :
    ¬ Function.Injective
      (coreColumnRealization (trivialCore Label) φ () (N := 1)) := by
  intro hinj
  have hconst :
      coreColumnRealization (trivialCore Label) φ () (N := 1)
          (FiniteColumnIndex.base : FiniteColumnIndex l 1) =
        coreColumnRealization (trivialCore Label) φ () (N := 1)
          (FiniteColumnIndex.ind3 1 (FiniteColumnIndex.base : FiniteColumnIndex l 1)) :=
    (trivialCore_coreColumnRealization φ
        (FiniteColumnIndex.base : FiniteColumnIndex l 1)).trans
      ((trivialCore_coreColumnRealization φ
        (FiniteColumnIndex.ind3 1
          (FiniteColumnIndex.base : FiniteColumnIndex l 1))).symm)
  have h := hinj hconst
  have hlevel := congrArg (fun x : FiniteColumnIndex l 1 => x.level.val) h
  simp only [FiniteColumnIndex.base_level, FiniteColumnIndex.ind3_level_val,
    Fin.val_zero, zero_add, Nat.min_self] at hlevel
  omega

/-- No left inverse exists over the trivial core, for any label map. -/
theorem trivialCore_no_leftInverse {l : PrimeGeFive} {Label : Type u}
    [AddGroup Label] (φ : finiteLabel l →+ Label) :
    ¬ RealizationLeftInverse (N := 1) (trivialCore Label) φ () :=
  fun h => trivialCore_no_injective_phi φ
    (coreColumnRealization_injective_of_leftInverse (trivialCore Label) φ () h)

/-- No readback exists over the trivial core, for any label map. -/
theorem trivialCore_no_readback {l : PrimeGeFive} {Label : Type u}
    [AddGroup Label] (φ : finiteLabel l →+ Label) :
    ¬ RealizationReadback (N := 1) (trivialCore Label) φ () :=
  fun h => trivialCore_no_leftInverse φ
    (readback_to_leftInverse (N := 1) (trivialCore Label) φ () h)

/-! ## Finite instance of the readback; trunk-factorization supply

Follow-up evaluation (2026-10-16).  The finite instance `(l, N)` over the
concrete source input `Input.concreteInput l` has *unconditional*
injectivity of the column realization: the realization is exactly the
injective trunk map `columnToProcessionChoice` (card
`IUT-III.finite-source-column-trunk-bridge`,
`columnToProcessionChoice_injective`).  Hence `RealizationLeftInverse` and
`RealizationReadback` are inhabited there with no hypothesis.  This closes
the identification-proper half for the concrete finite instance; the
label-to-`FPrimeStrip` interface remains outside, as before.

No Kummer/log-shell roundtrip is consumed: the strip-level arrows of
`Theorem311/SourceKummerEvaluationArrows.lean` (Kummer arrow, evaluation
arrow, reduced four-corner square) live over `FPrimeStrip` and
`TimesMuQuotient`; no map in this file family connects strip data to the
`Choice`-level readback, so they are not type-composable with
`RealizationReadback`.  The missing dictionary is exactly the forwarded
FPrimeStrip wiring request (supply side: IUT I prime-strip and IUT II
vertical log-Kummer lines).  For an arbitrary core, the conditional supply
landed here is a *faithful finite-trunk readout*: an injective `j` through
which the realization factors over `columnToProcessionChoice`.  It is a
technical reduction interface (finite surrogate for the source-side
identification of the Choice data; not a paper-named object) and it implies
the readback; it is inhabited by `concreteInput` with `j = id`.
-/

/-- Conditional supply for the readback: the realization is a faithful read
of the finite column trunk through an injective map `j` (a technical
reduction interface, not a paper-named object).  Inhabited unconditionally
by `concreteInput` (`concreteInput_trunkFactorization`). -/
def RealizationTrunkFactorization {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice)
    (φ : finiteLabel l →+ Label) (c₀ : Choice) : Prop :=
  ∃ j : ProcessionChoice l → Choice,
    Function.Injective j ∧
      ∀ x : FiniteColumnIndex l N,
        coreColumnRealization core φ c₀ x = j (columnToProcessionChoice l N x)

/-- A faithful trunk factorization yields the readback (hence injectivity,
by the minimality criterion `leftInverse_iff_injective`). -/
theorem readback_of_trunkFactorization {l : PrimeGeFive} {N : Nat}
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (h : RealizationTrunkFactorization (N := N) core φ c₀) :
    RealizationReadback (N := N) core φ c₀ := by
  obtain ⟨j, hj, hfac⟩ := h
  have hinj : Function.Injective (coreColumnRealization (N := N) core φ c₀) := by
    intro x y hxy
    have h2 : j (columnToProcessionChoice l N x) =
        j (columnToProcessionChoice l N y) := by
      rw [← hfac x, ← hfac y]
      exact hxy
    exact columnToProcessionChoice_injective l N (hj h2)
  exact readback_of_leftInverse core φ c₀
    (leftInverse_of_injective core φ c₀ hinj)

/-- Core-level form of the concrete-input specialization: the realization
over `Input.concreteInput l` IS the trunk map. -/
theorem concreteInput_coreColumnRealization_eq (l : PrimeGeFive) (N : Nat) :
    coreColumnRealization
        (SourceProcessionBoundary.Input.concreteInput l).carrier.core
        (AddMonoidHom.id (finiteLabel l))
        (SourceProcessionBoundary.Input.concreteInput l).carrier.core.base =
      columnToProcessionChoice l N := by
  funext x
  exact congrFun (concreteInput_inputColumnRealization_eq l N) x

/-- Unconditional injectivity of the realization over the concrete input. -/
theorem concreteInput_coreColumnRealization_injective (l : PrimeGeFive)
    (N : Nat) :
    Function.Injective
      (coreColumnRealization (N := N)
        (SourceProcessionBoundary.Input.concreteInput l).carrier.core
        (AddMonoidHom.id (finiteLabel l))
        (SourceProcessionBoundary.Input.concreteInput l).carrier.core.base) := by
  rw [concreteInput_coreColumnRealization_eq l N]
  exact columnToProcessionChoice_injective l N

/-- Unconditional injectivity at the input level (`inputColumnRealization`),
i.e. identification on the concrete finite instance. -/
theorem concreteInput_inputColumnRealization_injective (l : PrimeGeFive)
    (N : Nat) :
    Function.Injective
      (inputColumnRealization (SourceProcessionBoundary.Input.concreteInput l)
        (AddMonoidHom.id (finiteLabel l)) N) := by
  rw [concreteInput_inputColumnRealization_eq l N]
  exact columnToProcessionChoice_injective l N

/-- The concrete input inhabits the trunk-factorization supply (`j = id`). -/
theorem concreteInput_trunkFactorization (l : PrimeGeFive) (N : Nat) :
    RealizationTrunkFactorization (N := N)
      (SourceProcessionBoundary.Input.concreteInput l).carrier.core
      (AddMonoidHom.id (finiteLabel l))
      (SourceProcessionBoundary.Input.concreteInput l).carrier.core.base :=
  ⟨id, fun _ _ h => h, fun x =>
    congrFun (concreteInput_coreColumnRealization_eq l N) x⟩

/-- Finite instance: `RealizationReadback` holds for the concrete input. -/
theorem concreteInput_readback (l : PrimeGeFive) (N : Nat) :
    RealizationReadback (N := N)
      (SourceProcessionBoundary.Input.concreteInput l).carrier.core
      (AddMonoidHom.id (finiteLabel l))
      (SourceProcessionBoundary.Input.concreteInput l).carrier.core.base :=
  readback_of_trunkFactorization _ _ _
    (concreteInput_trunkFactorization l N)

/-- Finite instance, left-inverse form. -/
theorem concreteInput_leftInverse (l : PrimeGeFive) (N : Nat) :
    RealizationLeftInverse (N := N)
      (SourceProcessionBoundary.Input.concreteInput l).carrier.core
      (AddMonoidHom.id (finiteLabel l))
      (SourceProcessionBoundary.Input.concreteInput l).carrier.core.base :=
  leftInverse_of_injective _ _ _
    (concreteInput_coreColumnRealization_injective l N)

end SourceColumnRealization

namespace Audit

/-- Constructive half of the API-9 second-half obligation: the φ-parameterized
trunk realization over an arbitrary source input, with its structure laws and
the explicit level-bound handling. -/
def sourceColumnRealization : Obligation :=
  { id := "IUT-III.source-column-realization"
    source :=
      "DSH-F reconnaissance report, section API-9 (REPORT.md:588-598); " ++
        "paper: IUT III, Theorem 3.11 / Remark 3.11.1"
    status := VerificationStatus.provedKernel
    note :=
      "Constructive half of IUT-III.source-column-carrier-identification, " ++
        "proved as an ordinary algebraic kernel over an arbitrary source " ++
        "input: the canonical realization x |-> ind1 (φ x.procession) " ++
        "(ind2 (φ x.tensor) (ind3 x.level.val core.base)) with " ++
        "(Ind1)/(Ind2) intertwining, base law, level formula, the bounded " ++
        "(Ind3) law, and the concrete specialization to " ++
        "columnToProcessionChoice on concreteInput (φ = id). Level-bound " ++
        "verdict: unnecessary for (Ind1)/(Ind2)/base/level; for (Ind3) an " ++
        "explicit hypothesis, with a truncation obstruction showing it is " ++
        "not removable. The construction consumes only Input.carrier.core; " ++
        "theater/history/packet/target/route fields and the FPrimeStrip V " ++
        "data are not consumed. Unconditional injectivity is NOT included: a " ++
        "trivial-action counterexample over Unit shows the Core laws do " ++
        "not imply it (for every label map). The conditional form IS " ++
        "included in this file (audit card IUT-III.source-column-readback): " ++
        "under the readback hypothesis, equivalent to a left inverse and " ++
        "hence to injectivity, the realization is injective. Also NOT " ++
        "included: the label-to-FPrimeStrip-V interface, and any source " ++
        "existence (API-8 remains open; trap T7)."
    dependsOn :=
      [ "IUT-III.source-procession-boundary",
        "IUT-III.finite-source-column-trunk-bridge" ] }

/-- Conditional-injectivity (readback) half of the API-9 identification
obligation: injectivity of the canonical realization under the readback
hypothesis, which is equivalent to injectivity itself. -/
def sourceColumnReadback : Obligation :=
  { id := "IUT-III.source-column-readback"
    source :=
      "DSH-F reconnaissance report, section API-9 (REPORT.md:588-598); " ++
        "paper: IUT III, Theorem 3.11 / Remark 3.11.1 (finite-model side)"
    status := VerificationStatus.interface
    note :=
      "Conditional-injectivity half of IUT-III.source-column-carrier-" ++
        "identification. Proved: (i) the canonical realization is injective " ++
        "under the readback hypothesis RealizationReadback; (ii) readback, " ++
        "left-inverse existence and injectivity are equivalent predicates on " ++
        "the same data (leftInverse_iff_injective, readback_of_leftInverse), " ++
        "so the hypothesis is the weakest sufficient one (technical " ++
        "minimalization predicate; paper dictionary candidate = output " ++
        "faithfulness of IUT III Thm 3.11 / Rmk 3.11.1, to be confirmed by " ++
        "the paper owner); (iii) sharpness: for every label map the trivial " ++
        "core over Unit refutes injectivity, so some Choice-side hypothesis " ++
        "is necessary. NOT included: the unconditional statement (false as " ++
        "stated) and the label-to-FPrimeStrip-V interface. Finite " ++
        "instance (follow-up): concreteInput_readback proves " ++
        "RealizationReadback for concreteInput unconditionally, " ++
        "through the faithful trunk readout; " ++
        "RealizationTrunkFactorization implies the readback " ++
        "(readback_of_trunkFactorization); the general-input " ++
        "statement remains conditional."
    dependsOn :=
      [ "IUT-III.source-column-realization",
        "IUT-III.source-procession-boundary" ] }

end Audit

end

end LeanFormal.IUT
