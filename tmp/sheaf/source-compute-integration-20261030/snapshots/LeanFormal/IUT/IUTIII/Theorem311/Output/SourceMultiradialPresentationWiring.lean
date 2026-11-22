import LeanFormal.IUT.IUTIII.Theorem311.Output.CarrierConnectorSpecification
import LeanFormal.IUT.IUTIII.Theorem311.SourceMultiradialTwoActionEquivalence
import LeanFormal.IUT.IUTIII.Theorem311.ParametricCarrier
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteParameterized
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind2AlienCopySeparation
import Mathlib.Tactic

/-!
# Conditional wiring: source carrier to the multiradial presentation (card W)

Card W of the carrier connector specification (report section 16) asks for the
construction of the Step-XI facing records `SourceTheorem311MultiradialPresentation`
and `SourceTheorem311MultiradialAlgorithm` (SourceMultiradialTwoActionEquivalence.lean:149,
:199) from a source carrier together with an algorithm input.  This file
constructs those records **conditionally**: the carrier
(`ParametricTheorem311.Carrier`, carrying CC.1 `connector` and CC.2
`ind3_level_eq` as fields), the procession-automorphism datum W.1 and the
(Ind2) action datum W.4 are hypotheses; nothing is claimed unconditionally.
The connector instance CC.1 and the level-additivity CC.2 remain open at the
source level (CarrierConnectorSpecification.lean; report sections 16-17).

## Paper location

IUT III, Theorem 3.11, (i): the representation is constructed via an algorithm
in the procession of D-prime-strips that is functorial with respect to
isomorphisms of processions (corpus III.txt:9273-9276), after quotienting by
the (Ind1) automorphism indeterminacy of the procession (corpus III.txt:9258-9260)
and the (Ind2) indeterminacy (corpus III.txt:9261-9272); cf. Remark 3.11.1
(corpus III.txt:9619, (i) at :9620-9634) on functoriality and compatibility
with the permutation symmetries.

## Frozen statements (statement-first; proofs below)

Conditional on `carrier`, W.1 (`SourceProcessionAutomorphismData`: a group
action on the choices, level preserving, commuting with the (Ind1)/(Ind2)/(Ind3)
procession operations) and W.4 (`Ind2ActionData`: a commuting (Ind2) action),
the file constructs:

- `sourcePresentationOfCarrier carrier autom input` :
  `SourceTheorem311MultiradialPresentation G I n Choice` with
  `output := (runAlgorithm carrier input).target` and
  `processionAction := autom.act` (Output is the carrier choice type; the data
  (a), (b), (c) of the paper are *not* constructed, as in the reduced form);
- `sourceAlgorithmOfCarrier carrier autom ind2Data input` :
  `SourceTheorem311MultiradialAlgorithm G G2 I n Choice`;
- the composed entry points `sourcePresentationOfInputAndDatum` and
  `sourceAlgorithmOfInputAndDatum`, which take the seven-object boundary
  `DerivedPrerequisiteInput` plus the connector datum of
  `CarrierConnectorSpecification`.

W.2 (functoriality) is **proved**, not assumed:
`connector_route_realizes_automorphism` (every automorphism is realized by a
horizontal connector route; uses CC.1) and `automorphism_routeTarget` /
`automorphism_runAlgorithm_target` (the algorithm is functorial under procession
automorphisms; uses the commutation fields of W.1).

## W.3 status (recorded, not assumed)

The compatibility of the wiring with `OriginalInput.fPrimeStripAt`
(`sourceColumnProcession`, SourceMultiradialTwoActionEquivalence.lean:136) is
**not expressible** with the current interfaces: no correspondence between the
carrier choice type and `FPrimeStrip V` is modeled anywhere in the tree, so
W.3 has no statement to assume.  It is recorded as such in the report instead
of being smuggled in as a vacuous field.

## W.4: finite kernel form (section 5)

For the finite Q(i)-at-5 carrier (`SourceFiniteParameterized.carrier`) the
file now supplies W.1 and W.4 in kernel form: `finiteKernelProcessionAutomorphism`
(the (Ind1) translation action of the finite label group) and
`finiteKernelInd2ActionData` (the (Ind2) translation action).  The (Ind2)
action at `ofAdd shift` is identified with the native-to-alien link map of
`IUT-III.Ind2.concrete-alien-copy-separation` (`Ind2AlienCopy.ind2ShiftedCopy`,
`finiteKernelInd2ActionData_shift_agrees_linkMap`) and inherits its
nonzero-shift separation; `finiteKernelSourceAlgorithm` assembles the finite
kernel-form instance of the Step-XI facing record.  This is a finite
test-carrier supply: the source-level W.4 (Ism-equivariance of the actual
source link) remains open.
-/

namespace LeanFormal.IUT

noncomputable section

universe uG₁ uG₂ u v uv ua upi umon ui

namespace SourceMultiradialPresentationWiring

open MultiradialKernel
open MultiradialKernel.Core
open Theorem311Source

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v} [AddGroup Label]
variable {G₁ : Type uG₁} [Group G₁] {G₂ : Type uG₂} [Group G₂]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n : Int}

/-! ## 1. W.1 and W.4: the named hypotheses -/

/-- W.1: the (Ind1) automorphism datum of the procession at the carrier level.
    A group action on the choices which preserves the level and commutes with
    the (Ind1)/(Ind2)/(Ind3) operations of the procession; i.e. a group of
    automorphisms of the procession structure (corpus III.txt:9258-9260).
    This is a hypothesis type, not a construction. -/
structure SourceProcessionAutomorphismData
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (G : Type uG₁) [Group G] where
  act : G →* Equiv.Perm Choice
  act_level : ∀ g c, carrier.core.level (act g c) = carrier.core.level c
  act_ind1 : ∀ g (a : Label) c,
    act g (carrier.core.ind1 a c) = carrier.core.ind1 a (act g c)
  act_ind2 : ∀ g (a : Label) c,
    act g (carrier.core.ind2 a c) = carrier.core.ind2 a (act g c)
  act_ind3 : ∀ g (m : Nat) c,
    act g (carrier.core.ind3 m c) = carrier.core.ind3 m (act g c)

/-- W.4: the (Ind2) action datum: a commuting action of the (Ind2) group on
    the choices (corpus III.txt:9261-9272).  This is a hypothesis type, not a
    construction; the independence of the `Ism` copies of the paper is not
    modeled (reduced form). -/
structure Ind2ActionData (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (G₂ : Type uG₂) [Group G₂] where
  ind2 : G₂ →* Equiv.Perm Choice
  ind2_commute : ∀ (g₂ : G₂) (g₁ : G₁) (c : Choice),
    autom.act g₁ (ind2 g₂ c) = ind2 g₂ (autom.act g₁ c)

/-! ## 2. W.2, proved: connector realization and algorithm functoriality -/

/-- W.2a: every procession automorphism is realized by the horizontal connector
    route between `c` and `act g c` (uses CC.1, the connector field of the
    carrier). -/
theorem connector_route_realizes_automorphism
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (g : G₁) (c : Choice) :
    ParametricTheorem311.routeTarget carrier
        (carrier.connector c (autom.act g c)) c = autom.act g c :=
  ParametricTheorem311.connector_target carrier (autom.act_level g c).symm

/-- The realizing connector route is horizontal (uses CC.1). -/
theorem connector_route_realizes_automorphism_horizontal
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (g : G₁) (c : Choice) :
    ParametricTheorem311.horizontalRoute carrier
      (carrier.connector c (autom.act g c)) :=
  ParametricTheorem311.horizontalRoute_connector carrier c (autom.act g c)

/-- W.2b: the algorithm is functorial under procession automorphisms at the
    route-target level: running a route from the image choice is the image of
    the run. -/
theorem automorphism_routeTarget
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (g : G₁) (route : List (RouteStep Label)) (c : Choice) :
    autom.act g (ParametricTheorem311.routeTarget carrier route c) =
      ParametricTheorem311.routeTarget carrier route (autom.act g c) := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      rw [ParametricTheorem311.routeTarget_cons,
        ParametricTheorem311.routeTarget_cons]
      have hstep : autom.act g (applyStep carrier.core step c) =
          applyStep carrier.core step (autom.act g c) := by
        cases step with
        | ind1 a => exact autom.act_ind1 g a c
        | ind2 a => exact autom.act_ind2 g a c
        | ind3 m => exact autom.act_ind3 g m c
      rw [ih (applyStep carrier.core step c), hstep]

/-- W.2b at the algorithm interface: the run target from the shifted source is
    the image of the run target. -/
theorem automorphism_runAlgorithm_target
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (g : G₁) (input : ParametricTheorem311.AlgorithmInput carrier) :
    autom.act g (ParametricTheorem311.runAlgorithm carrier input).target =
      ParametricTheorem311.routeTarget carrier input.route
        (autom.act g input.source) := by
  rw [ParametricTheorem311.runAlgorithm_target,
    ParametricTheorem311.algorithmTarget]
  exact automorphism_routeTarget carrier autom g input.route input.source

/-! ## 3. The conditional presentation and algorithm records -/

/-- The conditional presentation: output is the run target, the procession
    action is the W.1 automorphism action (realized through connector routes by
    W.2a).  Conditional on `carrier` (CC.1 + CC.2), W.1 and the algorithm
    input; no unconditional claim. -/
def sourcePresentationOfCarrier
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (input : ParametricTheorem311.AlgorithmInput carrier) :
    SourceTheorem311MultiradialPresentation G₁ I n Choice where
  output := (ParametricTheorem311.runAlgorithm carrier input).target
  processionAction := autom.act

@[simp] theorem sourcePresentationOfCarrier_output
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (input : ParametricTheorem311.AlgorithmInput carrier) :
    (sourcePresentationOfCarrier (I := I) (n := n) carrier autom input).output =
      (ParametricTheorem311.runAlgorithm carrier input).target := rfl

@[simp] theorem sourcePresentationOfCarrier_processionAction
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (input : ParametricTheorem311.AlgorithmInput carrier) (g : G₁) :
    (sourcePresentationOfCarrier (I := I) (n := n) carrier autom input).processionAction g =
      autom.act g := rfl

/-- The procession action of the presentation factors through connector
    routes: applying `g` to a choice is the route target of the realizing
    connector route (W.2a). -/
theorem sourcePresentationOfCarrier_processionAction_apply
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (input : ParametricTheorem311.AlgorithmInput carrier) (g : G₁) (c : Choice) :
    (sourcePresentationOfCarrier (I := I) (n := n) carrier autom input).processionAction g c =
      ParametricTheorem311.routeTarget carrier
        (carrier.connector c (autom.act g c)) c :=
  (connector_route_realizes_automorphism carrier autom g c).symm

/-- Level bookkeeping of the presentation output: the level of the output is
    the level of the input source plus the vertical budget of the route (this
    is the point where CC.2, `ind3_level_eq`, is consumed). -/
theorem sourcePresentationOfCarrier_output_level
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (input : ParametricTheorem311.AlgorithmInput carrier) :
    carrier.core.level (sourcePresentationOfCarrier (I := I) (n := n) carrier autom input).output =
      carrier.core.level input.source +
        ParametricTheorem311.verticalBudget input.route := by
  rw [sourcePresentationOfCarrier_output,
    ParametricTheorem311.runAlgorithm_target, ParametricTheorem311.algorithmTarget]
  exact ParametricTheorem311.routeTarget_level_eq_budget carrier input.route input.source

/-- The conditional algorithm record: the presentation of
    `sourcePresentationOfCarrier` together with the W.4 (Ind2) action. -/
def sourceAlgorithmOfCarrier
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (ind2Data : Ind2ActionData carrier autom G₂)
    (input : ParametricTheorem311.AlgorithmInput carrier) :
    SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Choice where
  presentation := sourcePresentationOfCarrier carrier autom input
  ind2Action := ind2Data.ind2
  ind1_ind2_commute := fun g₁ g₂ o => ind2Data.ind2_commute g₂ g₁ o

/-! ## 4. Composed entry points from the seven-object boundary -/

/-- Composed conditional entry: the carrier is supplied through the connector
    datum of `CarrierConnectorSpecification` (CC.1 + CC.2 as the datum's
    fields), so this takes the source boundary plus the two named cards. -/
def sourcePresentationOfInputAndDatum
    (S : DerivedPrerequisiteInput Label Choice)
    (datum : CarrierConnectorSpecification.CarrierConnectorDatum S.core)
    (autom : SourceProcessionAutomorphismData
      (CarrierConnectorSpecification.sourceCarrierOfConnectorDatum S datum) G₁)
    (input : ParametricTheorem311.AlgorithmInput
      (CarrierConnectorSpecification.sourceCarrierOfConnectorDatum S datum)) :
    SourceTheorem311MultiradialPresentation G₁ I n Choice :=
  sourcePresentationOfCarrier
    (CarrierConnectorSpecification.sourceCarrierOfConnectorDatum S datum) autom input

/-- Composed conditional entry at the algorithm level (adds W.4). -/
def sourceAlgorithmOfInputAndDatum
    (S : DerivedPrerequisiteInput Label Choice)
    (datum : CarrierConnectorSpecification.CarrierConnectorDatum S.core)
    (autom : SourceProcessionAutomorphismData
      (CarrierConnectorSpecification.sourceCarrierOfConnectorDatum S datum) G₁)
    (ind2Data : Ind2ActionData
      (CarrierConnectorSpecification.sourceCarrierOfConnectorDatum S datum) autom G₂)
    (input : ParametricTheorem311.AlgorithmInput
      (CarrierConnectorSpecification.sourceCarrierOfConnectorDatum S datum)) :
    SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Choice :=
  sourceAlgorithmOfCarrier
    (CarrierConnectorSpecification.sourceCarrierOfConnectorDatum S datum)
    autom ind2Data input

/-! ## 5. W.4 in kernel form: the finite alien-copy translate -/

section FiniteKernelWiring

open ConcreteFiniteTheorem311

/-- Kernel form of the (Ind1) action at the finite model: translation of the
    procession label by the finite label group of the Q(i)-at-5 model. -/
def ind1KernelPerm (l : PrimeGeFive) (g : Multiplicative (finiteLabel l)) :
    Equiv.Perm (ProcessionChoice l) where
  toFun := ProcessionChoice.ind1Act (Multiplicative.toAdd g)
  invFun := ProcessionChoice.ind1Act (-(Multiplicative.toAdd g))
  left_inv := fun c => by simp
  right_inv := fun c => by simp

@[simp] theorem ind1KernelPerm_apply (l : PrimeGeFive)
    (g : Multiplicative (finiteLabel l)) (c : ProcessionChoice l) :
    ind1KernelPerm l g c =
      ProcessionChoice.ind1Act (Multiplicative.toAdd g) c :=
  rfl

/-- The (Ind1) kernel translation as a multiplicative action on the finite
    choices (the finite label group is written multiplicatively). -/
def ind1KernelAction (l : PrimeGeFive) :
    Multiplicative (finiteLabel l) →* Equiv.Perm (ProcessionChoice l) where
  toFun := ind1KernelPerm l
  map_one' := by
    ext c
    rw [Equiv.Perm.one_apply]
    exact ProcessionChoice.ind1_zero c
  map_mul' := by
    intro g h
    ext c
    rw [Equiv.Perm.mul_apply]
    exact ProcessionChoice.ind1_add (Multiplicative.toAdd g)
      (Multiplicative.toAdd h) c

@[simp] theorem ind1KernelAction_apply (l : PrimeGeFive)
    (g : Multiplicative (finiteLabel l)) (c : ProcessionChoice l) :
    ind1KernelAction l g c =
      ProcessionChoice.ind1Act (Multiplicative.toAdd g) c :=
  rfl

/-- Kernel form of the (Ind2) action at the finite model: translation of the
    tensor label by the finite label group. -/
def ind2KernelPerm (l : PrimeGeFive) (g : Multiplicative (finiteLabel l)) :
    Equiv.Perm (ProcessionChoice l) where
  toFun := ProcessionChoice.ind2Act (Multiplicative.toAdd g)
  invFun := ProcessionChoice.ind2Act (-(Multiplicative.toAdd g))
  left_inv := fun c => by simp
  right_inv := fun c => by simp

@[simp] theorem ind2KernelPerm_apply (l : PrimeGeFive)
    (g : Multiplicative (finiteLabel l)) (c : ProcessionChoice l) :
    ind2KernelPerm l g c =
      ProcessionChoice.ind2Act (Multiplicative.toAdd g) c :=
  rfl

/-- The (Ind2) kernel translation as a multiplicative action on the finite
    choices. -/
def ind2KernelAction (l : PrimeGeFive) :
    Multiplicative (finiteLabel l) →* Equiv.Perm (ProcessionChoice l) where
  toFun := ind2KernelPerm l
  map_one' := by
    ext c
    rw [Equiv.Perm.one_apply]
    exact ProcessionChoice.ind2_zero c
  map_mul' := by
    intro g h
    ext c
    rw [Equiv.Perm.mul_apply]
    exact ProcessionChoice.ind2_add (Multiplicative.toAdd g)
      (Multiplicative.toAdd h) c

@[simp] theorem ind2KernelAction_apply (l : PrimeGeFive)
    (g : Multiplicative (finiteLabel l)) (c : ProcessionChoice l) :
    ind2KernelAction l g c =
      ProcessionChoice.ind2Act (Multiplicative.toAdd g) c :=
  rfl

/-- W.1 in kernel form at the finite carrier: the finite label group acts by
    (Ind1) translation, preserving the level and commuting with the
    (Ind1)/(Ind2)/(Ind3) operations. -/
def finiteKernelProcessionAutomorphism (l : PrimeGeFive) :
    SourceProcessionAutomorphismData (SourceFiniteParameterized.carrier l)
      (Multiplicative (finiteLabel l)) where
  act := ind1KernelAction l
  act_level := by
    intro g c
    simp only [SourceFiniteParameterized.carrier_core,
      SourceFiniteMultiradial.core_level, ind1KernelAction_apply,
      ProcessionChoice.ind1_upperSemiLevel]
  act_ind1 := by
    intro g a c
    simp only [SourceFiniteParameterized.carrier_core,
      SourceFiniteMultiradial.core_ind1, ind1KernelAction_apply]
    rw [← ProcessionChoice.ind1_add (Multiplicative.toAdd g) a c,
      ← ProcessionChoice.ind1_add a (Multiplicative.toAdd g) c,
      add_comm (Multiplicative.toAdd g) a]
  act_ind2 := by
    intro g a c
    simp only [SourceFiniteParameterized.carrier_core,
      SourceFiniteMultiradial.core_ind2, ind1KernelAction_apply]
    exact ProcessionChoice.ind1_ind2_commute (Multiplicative.toAdd g) a c
  act_ind3 := by
    intro g m c
    simp only [SourceFiniteParameterized.carrier_core,
      SourceFiniteMultiradial.core_ind3, ind1KernelAction_apply]
    exact ProcessionChoice.ind1_ind3_commute (Multiplicative.toAdd g) m c

/-- W.4 in kernel form at the finite carrier: the (Ind2) translation action,
    commuting with the (Ind1) translation action. -/
def finiteKernelInd2ActionData (l : PrimeGeFive) :
    Ind2ActionData (SourceFiniteParameterized.carrier l)
      (finiteKernelProcessionAutomorphism l)
      (Multiplicative (finiteLabel l)) where
  ind2 := ind2KernelAction l
  ind2_commute := by
    intro g₂ g₁ c
    simp only [finiteKernelProcessionAutomorphism, ind1KernelAction_apply,
      ind2KernelAction_apply]
    exact ProcessionChoice.ind1_ind2_commute (Multiplicative.toAdd g₁)
      (Multiplicative.toAdd g₂) c

@[simp] theorem finiteKernelInd2ActionData_ind2_apply (l : PrimeGeFive)
    (g : Multiplicative (finiteLabel l)) (c : ProcessionChoice l) :
    (finiteKernelInd2ActionData l).ind2 g c =
      ProcessionChoice.ind2Act (Multiplicative.toAdd g) c :=
  rfl

@[simp] theorem finiteKernelInd2ActionData_shift_apply (l : PrimeGeFive)
    (shift : finiteLabel l) (c : ProcessionChoice l) :
    (finiteKernelInd2ActionData l).ind2 (Multiplicative.ofAdd shift) c =
      ProcessionChoice.ind2Act shift c :=
  rfl

/-- Shape match between card W.4 and the Q(i)-at-5 alien-copy construction
    (`IUT-III.Ind2.concrete-alien-copy-separation`): the wired (Ind2) action
    at the shift translate is exactly the native-to-alien link map of
    `Ind2AlienCopy.ind2ShiftedCopy`. -/
theorem finiteKernelInd2ActionData_shift_agrees_linkMap (l : PrimeGeFive)
    (shift : finiteLabel l) (c : ProcessionChoice l) :
    (finiteKernelInd2ActionData l).ind2 (Multiplicative.ofAdd shift) c =
      (Ind2AlienCopy.ind2ShiftedCopy l shift).linkMap c := by
  rw [finiteKernelInd2ActionData_shift_apply,
    Ind2AlienCopy.ind2ShiftedCopy_linkMap_apply]

/-- The nonzero-shift separation of the Leibniz alien copy
    (`Ind2AlienCopy.ind2ShiftedCopy_linkMap_base_ne`) transfers to the wired
    (Ind2) action: at a nonzero shift the action moves the base choice. -/
theorem finiteKernelInd2ActionData_shift_base_ne (l : PrimeGeFive)
    (shift : finiteLabel l) (hshift : shift ≠ 0) :
    (finiteKernelInd2ActionData l).ind2 (Multiplicative.ofAdd shift)
      ProcessionChoice.base ≠ ProcessionChoice.base := by
  rw [finiteKernelInd2ActionData_shift_apply]
  exact Ind2AlienCopy.ind2ShiftedCopy_linkMap_base_ne l shift hshift

/-- The wired (Ind2) action is nontrivial with an explicit witness: the
    proved generator of the finite label group gives an element acting
    nontrivially on the base choice. -/
theorem finiteKernelInd2ActionData_nontrivial (l : PrimeGeFive) :
    ∃ g : Multiplicative (finiteLabel l), g ≠ 1 ∧
      (finiteKernelInd2ActionData l).ind2 g ProcessionChoice.base ≠
        ProcessionChoice.base := by
  refine ⟨Multiplicative.ofAdd (ConcreteSourceEtaleThetaBridge.generator l),
    ?_, ?_⟩
  · intro h
    have h' : ConcreteSourceEtaleThetaBridge.generator l = 0 := by
      simpa using congrArg Multiplicative.toAdd h
    exact ConcreteSourceEtaleThetaBridge.generator_ne_zero l h'
  · exact finiteKernelInd2ActionData_shift_base_ne l
      (ConcreteSourceEtaleThetaBridge.generator l)
      (ConcreteSourceEtaleThetaBridge.generator_ne_zero l)

/-- The conditional presentation with W.1 supplied by the finite kernel
    translation action. -/
def finiteKernelSourcePresentation (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l)) :
    SourceTheorem311MultiradialPresentation (Multiplicative (finiteLabel l))
      I n (ProcessionChoice l) :=
  sourcePresentationOfCarrier (I := I) (n := n)
    (SourceFiniteParameterized.carrier l) (finiteKernelProcessionAutomorphism l)
    input

/-- The finite kernel-form instance of the Step-XI facing algorithm record:
    carrier, W.1 and W.4 are all supplied by the finite Q(i)-at-5 model, with
    the (Ind2) action identified with the alien-copy link map.  Reduced form:
    the output is the carrier choice type and the data (a), (b), (c) are not
    constructed. -/
def finiteKernelSourceAlgorithm (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l)) :
    SourceTheorem311MultiradialAlgorithm (Multiplicative (finiteLabel l))
      (Multiplicative (finiteLabel l)) I n (ProcessionChoice l) :=
  sourceAlgorithmOfCarrier (I := I) (n := n)
    (SourceFiniteParameterized.carrier l) (finiteKernelProcessionAutomorphism l)
    (finiteKernelInd2ActionData l) input

end FiniteKernelWiring

/-! ## 6. APT-1 finite test: the non-trivial adjacent-column comparison

Card APT (`IUT-III.source-algorithmic-parallel-transport`, APT.lean:163) asks
for the comparison `SourceTheorem311TwoActionEquivalence A A'` between the
algorithm instances of two adjacent columns, together with the SHE landing
datum.  This section supplies the comparison field in the finite Q(i)-at-5
model, taking non-trivial values: the two instances are the finite kernel-form
algorithms of section 5 at the adjacent columns `n` and `n + 1`, and the
output equivalence is the (Ind2) kernel translate `ofAdd shift`, which
intertwines both actions (proved below) and is non-identity at any nonzero
shift.  Reduced form, explicitly: the actual source-level algorithm
instances, the adjacent-column procession isomorphism and the SHE landing
datum are not constructed; they remain the named card
`IUT-III.source-APT-transport-supply` (APT.lean:457). -/

section FiniteKernelComparison

open ConcreteFiniteTheorem311

/-- Action-compatibility in `Equiv.Perm` form: the (Ind2) kernel translate is
    equivariant for the (Ind1) kernel action. -/
theorem ind2KernelPerm_commutes_ind1 (l : PrimeGeFive)
    (shift g : Multiplicative (finiteLabel l)) (c : ProcessionChoice l) :
    ind2KernelPerm l shift (ind1KernelPerm l g c) =
      ind1KernelPerm l g (ind2KernelPerm l shift c) := by
  simp only [ind2KernelPerm_apply, ind1KernelPerm_apply]
  exact (ProcessionChoice.ind1_ind2_commute (Multiplicative.toAdd g)
    (Multiplicative.toAdd shift) c).symm

/-- The (Ind2) kernel translates commute with each other, in `Equiv.Perm`
    form. -/
theorem ind2KernelPerm_commutes_ind2 (l : PrimeGeFive)
    (shift g : Multiplicative (finiteLabel l)) (c : ProcessionChoice l) :
    ind2KernelPerm l shift (ind2KernelPerm l g c) =
      ind2KernelPerm l g (ind2KernelPerm l shift c) := by
  simp only [ind2KernelPerm_apply, ← ProcessionChoice.ind2_add]
  exact congrArg (fun h => ProcessionChoice.ind2Act h c)
    (add_comm (Multiplicative.toAdd shift) (Multiplicative.toAdd g))

/-- The plain-action form of the Leibniz alien-copy separation: the (Ind2)
    translate moves the base choice at any nonzero shift. -/
theorem ind2Act_shift_base_ne (l : PrimeGeFive) (shift : finiteLabel l)
    (hshift : shift ≠ 0) :
    ProcessionChoice.ind2Act shift ProcessionChoice.base ≠ ProcessionChoice.base := by
  intro h
  rw [← finiteKernelInd2ActionData_shift_apply] at h
  exact finiteKernelInd2ActionData_shift_base_ne l shift hshift h

/-- The empty-route algorithm input at a given finite choice: the finite test
    input of the adjacent-column comparison. -/
def finiteKernelComparisonInput (l : PrimeGeFive) (source : ProcessionChoice l) :
    ParametricTheorem311.AlgorithmInput (SourceFiniteParameterized.carrier l) where
  source := source
  route := []
  source_image_nonempty :=
    (SourceFiniteParameterized.carrier l).profile.possibleImage_nonempty source

@[simp] theorem finiteKernelComparisonInput_source (l : PrimeGeFive)
    (source : ProcessionChoice l) :
    (finiteKernelComparisonInput l source).source = source :=
  rfl

@[simp] theorem finiteKernelComparisonInput_route (l : PrimeGeFive)
    (source : ProcessionChoice l) :
    (finiteKernelComparisonInput l source).route = [] :=
  rfl

/-- Computation law: the (Ind1) action of the finite kernel-form algorithm is
    the (Ind1) kernel translate. -/
@[simp] theorem finiteKernelSourceAlgorithm_ind1Action_apply (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l))
    (g : Multiplicative (finiteLabel l)) (c : ProcessionChoice l) :
    (finiteKernelSourceAlgorithm l I n input).ind1Action g c =
      ProcessionChoice.ind1Act (Multiplicative.toAdd g) c :=
  rfl

/-- Computation law: the (Ind2) action of the finite kernel-form algorithm is
    the (Ind2) kernel translate. -/
@[simp] theorem finiteKernelSourceAlgorithm_ind2Action_apply (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l))
    (g : Multiplicative (finiteLabel l)) (c : ProcessionChoice l) :
    (finiteKernelSourceAlgorithm l I n input).ind2Action g c =
      ProcessionChoice.ind2Act (Multiplicative.toAdd g) c :=
  rfl

/-- Computation law: the presentation output of the finite kernel-form
    algorithm at the comparison input is the chosen source. -/
@[simp] theorem finiteKernelSourceAlgorithm_output_apply (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (source : ProcessionChoice l) :
    (finiteKernelSourceAlgorithm l I n
      (finiteKernelComparisonInput l source)).presentation.output = source :=
  rfl

/-- Frozen statement (finite test form; reduced): the non-trivial
    adjacent-column comparison of the finite kernel-form algorithm instances.
    The first instance runs at column `n` from `source`; the second at column
    `n + 1` from the (Ind2) translate `ind2Act shift source`; the output
    equivalence is the (Ind2) kernel translate by `ofAdd shift`, intertwining
    both actions.  At nonzero `shift` the comparison is non-identity on the
    base output (`finiteKernelTwoColumnComparison_nontrivial`). -/
def finiteKernelTwoColumnComparison (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (shift : finiteLabel l) (source : ProcessionChoice l) :
    SourceTheorem311TwoActionEquivalence
      (finiteKernelSourceAlgorithm l I n (finiteKernelComparisonInput l source))
      (finiteKernelSourceAlgorithm l I (n + 1)
        (finiteKernelComparisonInput l (ProcessionChoice.ind2Act shift source))) where
  ind1GroupEquiv := MulEquiv.refl (Multiplicative (finiteLabel l))
  outputEquiv := ind2KernelPerm l (Multiplicative.ofAdd shift)
  preserves_ind1 := by
    intro g o
    change ind2KernelPerm l (Multiplicative.ofAdd shift) (ind1KernelPerm l g o) =
      ind1KernelPerm l g (ind2KernelPerm l (Multiplicative.ofAdd shift) o)
    exact ind2KernelPerm_commutes_ind1 l (Multiplicative.ofAdd shift) g o
  preserves_ind2 := by
    intro g o
    change ind2KernelPerm l (Multiplicative.ofAdd shift) (ind2KernelPerm l g o) =
      ind2KernelPerm l g (ind2KernelPerm l (Multiplicative.ofAdd shift) o)
    exact ind2KernelPerm_commutes_ind2 l (Multiplicative.ofAdd shift) g o

@[simp] theorem finiteKernelTwoColumnComparison_outputEquiv_apply
    (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (shift : finiteLabel l) (source o : ProcessionChoice l) :
    (finiteKernelTwoColumnComparison l I n shift source).outputEquiv o =
      ProcessionChoice.ind2Act shift o :=
  rfl

/-- The comparison carries the first column's output to the second column's
    output. -/
theorem finiteKernelTwoColumnComparison_target_law (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (shift : finiteLabel l) (source : ProcessionChoice l) :
    (finiteKernelTwoColumnComparison l I n shift source).outputEquiv
        (finiteKernelSourceAlgorithm l I n
          (finiteKernelComparisonInput l source)).presentation.output =
      (finiteKernelSourceAlgorithm l I (n + 1)
        (finiteKernelComparisonInput l
          (ProcessionChoice.ind2Act shift source))).presentation.output := by
  simp only [finiteKernelSourceAlgorithm_output_apply,
    finiteKernelTwoColumnComparison_outputEquiv_apply]

/-- Non-triviality of the frozen comparison: at any nonzero shift the output
    equivalence moves the base output. -/
theorem finiteKernelTwoColumnComparison_nontrivial (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (shift : finiteLabel l) (hshift : shift ≠ 0) (source : ProcessionChoice l) :
    (finiteKernelTwoColumnComparison l I n shift source).outputEquiv
      ProcessionChoice.base ≠ ProcessionChoice.base := by
  simp only [finiteKernelTwoColumnComparison_outputEquiv_apply]
  exact ind2Act_shift_base_ne l shift hshift

/-- The comparison output equivalence is not the identity equivalence at any
    nonzero shift. -/
theorem finiteKernelTwoColumnComparison_outputEquiv_ne_refl (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (shift : finiteLabel l) (hshift : shift ≠ 0) (source : ProcessionChoice l) :
    (finiteKernelTwoColumnComparison l I n shift source).outputEquiv ≠
      Equiv.refl (ProcessionChoice l) := by
  intro h
  have hbase : (finiteKernelTwoColumnComparison l I n shift source).outputEquiv
      ProcessionChoice.base = ProcessionChoice.base := by
    simp [h]
  exact finiteKernelTwoColumnComparison_nontrivial l I n shift hshift source hbase

/-- A nontrivial adjacent-column comparison exists with an explicit witness:
    the proved generator of the finite label group supplies the nonzero
    shift. -/
theorem finiteKernelTwoColumnComparison_nontrivial_exists (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (source : ProcessionChoice l) :
    ∃ shift : finiteLabel l,
      (finiteKernelTwoColumnComparison l I n shift source).outputEquiv
        ProcessionChoice.base ≠ ProcessionChoice.base :=
  ⟨ConcreteSourceEtaleThetaBridge.generator l,
    finiteKernelTwoColumnComparison_nontrivial l I n
      (ConcreteSourceEtaleThetaBridge.generator l)
      (ConcreteSourceEtaleThetaBridge.generator_ne_zero l) source⟩

end FiniteKernelComparison

end SourceMultiradialPresentationWiring

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the conditional source-presentation wiring (card W). -/
def sourceMultiradialPresentationWiringRecord : Obligation :=
  { id := "IUT-III.multiradial-algorithm.source-presentation-wiring"
    source :=
      "IUT III, Theorem 3.11, (i) (corpus III.txt:9164, :9258-9260, " ++
        ":9261-9272, :9273-9276); Remark 3.11.1 (corpus III.txt:9619)"
    status := VerificationStatus.conditional
    note :=
      "Card W of the carrier connector specification is wired conditionally: " ++
        "`sourcePresentationOfCarrier` and `sourceAlgorithmOfCarrier` build " ++
        "the Step-XI facing records from a source carrier (CC.1 + CC.2 " ++
        "packaged as `ParametricTheorem311.Carrier`), the procession " ++
        "automorphism datum W.1 (`SourceProcessionAutomorphismData`) and the " ++
        "(Ind2) datum W.4 (`Ind2ActionData`); the output is the run target of " ++
        "`runAlgorithm` and the procession action is realized through " ++
        "connector routes (W.2, proved: " ++
        "`connector_route_realizes_automorphism`, `automorphism_routeTarget`, " ++
        "`automorphism_runAlgorithm_target`).  No unconditional instance is " ++
        "claimed; the carrier, W.1 and W.4 remain hypotheses.  W.3 " ++
        "(`OriginalInput.fPrimeStripAt` compatibility) is not expressible with " ++
        "the current interfaces and is recorded, not assumed.  The output " ++
        "type is the carrier choice type; the data (a), (b), (c) are not " ++
        "constructed (reduced form)."
    dependsOn :=
      [ "IUT-III.multiradial-algorithm",
        "IUT-III.multiradial-algorithm.carrier-connector-specification",
        "IUT-III.theorem-3.11-explicit-prerequisite-boundary",
        "IUT-III.multiradial-algorithm.general-route-normal-form" ] }

/-- Audit record for the finite kernel-form supply of card W.4: the (Ind2)
    action wired as the Q(i)-at-5 alien-copy translate, with the shape match
    to `IUT-III.Ind2.concrete-alien-copy-separation`. -/
def sourceMultiradialPresentationWiringInd2KernelRecord : Obligation :=
  { id := "IUT-III.multiradial-algorithm.source-presentation-wiring.ind2-kernel-form"
    source :=
      "IUT III, Theorem 3.11, (i) (corpus III.txt:9261-9272, the (Ind2) " ++
        "indeterminacy through independent copies of Ism); IUT II, " ++
        "Proposition 1.2, (vi) (Ism); Q(i)-at-5 finite model " ++
        "(ConcreteFiniteModel.lean)"
    status := VerificationStatus.testCarrier
    note :=
      "W.4 (`Ind2ActionData`) is supplied in kernel form for the finite " ++
        "Q(i)-at-5 carrier (`SourceFiniteParameterized.carrier`): " ++
        "`finiteKernelProcessionAutomorphism` fills W.1 by the (Ind1) " ++
        "translation action, `finiteKernelInd2ActionData` fills W.4 by the " ++
        "(Ind2) translation action, and " ++
        "`finiteKernelInd2ActionData_shift_agrees_linkMap` identifies the " ++
        "wired action at `ofAdd shift` with the native-to-alien link map of " ++
        "`IUT-III.Ind2.concrete-alien-copy-separation` " ++
        "(`Ind2AlienCopy.ind2ShiftedCopy`).  The nonzero-shift separation " ++
        "(`finiteKernelInd2ActionData_shift_base_ne`, " ++
        "`finiteKernelInd2ActionData_nontrivial`) transfers to the wired " ++
        "datum, and `finiteKernelSourceAlgorithm` assembles the finite " ++
        "kernel-form instance of the Step-XI facing record with the " ++
        "connector and level-additivity supplied by the finite carrier.  " ++
        "Finite test-carrier supply only: the source-level W.4 " ++
        "(Ism-equivariance of the actual source link) remains open, and the " ++
        "output is the carrier choice type with the data (a), (b), (c) not " ++
        "constructed (reduced form)."
    dependsOn :=
      [ "IUT-III.Ind2.concrete-alien-copy-separation",
        "IUT-III.multiradial-algorithm.source-presentation-wiring" ] }

/-- Audit record for the APT-1 finite test: the non-trivial adjacent-column
    comparison of the finite kernel-form algorithm instances (comparison
    field of Card APT, `IUT-III.source-algorithmic-parallel-transport`). -/
def sourceMultiradialPresentationWiringAptComparisonRecord : Obligation :=
  { id := "IUT-III.multiradial-algorithm.source-presentation-wiring.apt-comparison-test"
    source :=
      "IUT III, Theorem 3.11, (i); Remark 3.11.1, (ii) (etale-picture " ++
        "permutation symmetries, corpus III.txt:9843-9907); Card APT " ++
        "(APT.lean:163, comparison field at :169)"
    status := VerificationStatus.testCarrier
    note :=
      "APT-1 finite test in the Q(i)-at-5 model: " ++
        "`finiteKernelTwoColumnComparison` builds a " ++
        "`SourceTheorem311TwoActionEquivalence` between the finite " ++
        "kernel-form algorithm instances at the adjacent columns `n` and " ++
        "`n + 1` (section 5, `finiteKernelSourceAlgorithm`), with output " ++
        "equivalence the (Ind2) kernel translate `ofAdd shift`.  The " ++
        "comparison intertwines both actions (proved: " ++
        "`ind2KernelPerm_commutes_ind1`, `ind2KernelPerm_commutes_ind2`) " ++
        "and carries the first column's output to the second column's " ++
        "output (`finiteKernelTwoColumnComparison_target_law`); at any " ++
        "nonzero shift it is non-identity on the base output " ++
        "(`finiteKernelTwoColumnComparison_nontrivial`, and an explicit " ++
        "nonzero shift exists: " ++
        "`finiteKernelTwoColumnComparison_nontrivial_exists`).  Reduced " ++
        "form, finite test only: the actual source-level algorithm " ++
        "instances, the adjacent-column procession isomorphism and the " ++
        "SHE landing datum are NOT constructed; the source-level " ++
        "transport remains the named card " ++
        "`IUT-III.source-APT-transport-supply` (APT.lean:457).  No " ++
        "unconditional or source-level claim."
    dependsOn :=
      [ "IUT-III.multiradial-algorithm.source-presentation-wiring.ind2-kernel-form",
        "IUT-III.source-algorithmic-parallel-transport" ] }

end LeanFormal.IUT.Audit
