/-
  # Theorem 3.11 multiradial output: reduction pass

  Targets (frozen obligation records, `LeanFormal/IUT/IUTIII/Theorem311/`):

  * `IUT-III.theorem-3.11-output` (`Obligations.lean`): "Construct the
    multiradial output over the actual IUT I-II data" - paper source: IUT III,
    Theorem 3.11, (i) ("Multiradial Representation"), together with the
    log-Kummer correspondence (ii) and the Theta-times-mu-LGP-link
    compatibility (iii).
  * `IUT-III.multiradial-algorithm` (`Output/MultiradialAlgorithm.lean`):
    "Implement the algorithm and its output invariants" - paper source: the
    final paragraph of Theorem 3.11, (i) ("`n,oR_LGP` may be constructed via
    an algorithm in the procession of D-prime-strips ... that is functorial
    with respect to isomorphisms of processions of D-prime-strips"), and the
    indeterminacies (Ind1), (Ind2) of Theorem 3.11, (i) together with the
    upper-semi compatibility (Ind3) of Theorem 3.11, (ii).

  Paper terminology used in this file (IUT III):

  * (Ind1) automorphisms of the procession of D-prime-strips;
  * (Ind2) independent copies of Ism on direct summands;
  * (Ind3) upper-semi compatibility of the (a)-isomorphisms as m varies,
    with inclusions at v in V_non and surjections at v in V_arc;
  * IPL ("Input prime-strip link") and SHE ("Simultaneous holomorphic
    expressibility"), APT ("Algorithmic parallel transport") of
    Remark 3.11.1, (iii), (iv) - the north-wall consumers.

  What this reduction proves, and what it does not:

  * Proved (unconditional, kernel and carrier level): the route construction
    commutes with the (Ind3) log-link action for an arbitrary label group,
    and with the (Ind1)/(Ind2) actions for commutative label groups
    (`applyRoute_ind3_commute`, `applyRoute_ind1_commute`,
    `applyRoute_ind2_commute`); the algorithm `runAlgorithm` is total with
    all of its output invariants (`carrierAlgorithmContract`).  The (Ind1)
    double-step commutation is not a consequence of the frozen `Core` axioms
    for a non-commutative label group (it is equivalent to `g + h = h + g`);
    the finite Q(i)-at-5 labels `Fl l = ZMod l` are commutative.  These are
    statements about the frozen kernel interface of this repository, not
    about the paper's actual F-prime-strips.
  * Proved (conditional on the explicit source prerequisite package): the
    assembled output `Theorem311Source.theorem311Output` satisfies the
    field-level law bundle `SourceOutputLawBundle`
    (`theorem311Output_sourceLawBundle`, `sourceMultiradialOutputDischarge`).
    This is a reduction: the obligation is discharged once the package
    `Theorem311Source.Input` is instantiated; this file does not construct
    that package from the actual IUT I-II data.
  * Proved (finite Q(i)-at-5 carrier only): `finiteMultiradialAlgorithmDischarge`
    bundles the algorithm contract, the route normal form, and the
    Ind1/Ind2/Ind3 quotient laws for the single concrete carrier.
  * Not claimed: any general-source instance of `Theorem311Source.Input`, any
    general route normal form, or any identification of the kernel actions
    `ind1/ind2/ind3` with the paper's actual procession automorphisms beyond
    the frozen law interface.  See the two Audit records at the end.

  All declarations below are proved; this file introduces no extra unfounded
  assumption and no placeholder theorem.
-/

import LeanFormal.IUT.IUTIII.Theorem311.ParametricCarrier
import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteParameterized
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithm
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v

namespace MultiradialAlgorithmReduction

open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311

/-! ## 1. Functoriality of the route construction under (Ind1), (Ind2), (Ind3)

  Theorem 3.11, (i), requires the multiradial construction to be *functorial
  with respect to isomorphisms of processions of D-prime-strips*; the
  indeterminacies (Ind1) and (Ind2) act on the input data, and (Ind3) is the
  upper-semi compatibility of the log-link direction (Theorem 3.11, (ii)).
  At the kernel interface of this repository the three actions are
  `Core.ind1` (a group action), `Core.ind2` (a group action) and `Core.ind3`
  (a monoid action, one-sided on the level).  The following theorems show
  that the route construction `applyRoute` commutes with each of them; these
  are the kernel-level functoriality clauses.

  Commutativity note: the double-step commutation of the (Ind1) (and (Ind2))
  action, `ind1 g (ind1 h c) = ind1 h (ind1 g c)`, is *not* a consequence of
  the frozen `Core` axioms when the label group is non-commutative (it is
  equivalent to `g + h = h + g`, and `ind1 g c = g^(-1) + c` on a non-abelian
  group satisfies the axioms without it).  The finite Q(i)-at-5 labels
  `Fl l = ZMod l` are commutative, so the (Ind1)/(Ind2) theorems below are
  stated for commutative label groups.  The (Ind3) statements need no
  commutativity and are stated for an arbitrary `AddGroup`. -/

section CommutativeLabels

variable {Label : Type u} {Choice : Type v} [AddCommGroup Label]

/-- (Ind1) functoriality: the route construction commutes with the procession
    automorphism action.  Paper: IUT III, Theorem 3.11, (i) (final
    paragraph: functoriality with respect to isomorphisms of processions of
    D-prime-strips; indeterminacy (Ind1)). -/
theorem applyRoute_ind1_commute (core : Core Label Choice)
    (route : List (RouteStep Label)) (g : Label) (c : Choice) :
    applyRoute core route (core.ind1 g c) =
      core.ind1 g (applyRoute core route c) := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | ind1 h =>
          change applyRoute core rest (core.ind1 h (core.ind1 g c)) =
            core.ind1 g (applyRoute core rest (core.ind1 h c))
          have hstep : core.ind1 h (core.ind1 g c) =
              core.ind1 g (core.ind1 h c) := by
            rw [← core.ind1_add g h c, ← core.ind1_add h g c, add_comm g h]
          rw [hstep]
          exact ih (core.ind1 h c)
      | ind2 h =>
          change applyRoute core rest (core.ind2 h (core.ind1 g c)) =
            core.ind1 g (applyRoute core rest (core.ind2 h c))
          rw [← core.ind1_ind2_commute g h c]
          exact ih (core.ind2 h c)
      | ind3 n =>
          change applyRoute core rest (core.ind3 n (core.ind1 g c)) =
            core.ind1 g (applyRoute core rest (core.ind3 n c))
          rw [← core.ind1_ind3_commute g n c]
          exact ih (core.ind3 n c)

/-- (Ind2) functoriality: the route construction commutes with the Ism-copy
    action on the direct summands.  Paper: IUT III, Theorem 3.11, (i)
    (indeterminacy (Ind2)). -/
theorem applyRoute_ind2_commute (core : Core Label Choice)
    (route : List (RouteStep Label)) (g : Label) (c : Choice) :
    applyRoute core route (core.ind2 g c) =
      core.ind2 g (applyRoute core route c) := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | ind1 h =>
          change applyRoute core rest (core.ind1 h (core.ind2 g c)) =
            core.ind2 g (applyRoute core rest (core.ind1 h c))
          rw [core.ind1_ind2_commute h g c]
          exact ih (core.ind1 h c)
      | ind2 h =>
          change applyRoute core rest (core.ind2 h (core.ind2 g c)) =
            core.ind2 g (applyRoute core rest (core.ind2 h c))
          have hstep : core.ind2 h (core.ind2 g c) =
              core.ind2 g (core.ind2 h c) := by
            rw [← core.ind2_add g h c, ← core.ind2_add h g c, add_comm g h]
          rw [hstep]
          exact ih (core.ind2 h c)
      | ind3 n =>
          change applyRoute core rest (core.ind3 n (core.ind2 g c)) =
            core.ind2 g (applyRoute core rest (core.ind3 n c))
          rw [← core.ind2_ind3_commute g n c]
          exact ih (core.ind3 n c)

/-- The output log-volume of the route construction is invariant under the
    (Ind1) action on the input data.  Paper: IUT III, Theorem 3.11, (i),
    data (a) with the procession-normalized log-volumes of Proposition 3.9. -/
theorem applyRoute_ind1_commute_logVolume (core : Core Label Choice)
    (profile : Profile core) (route : List (RouteStep Label))
    (g : Label) (c : Choice) :
    profile.logVolume (applyRoute core route (core.ind1 g c)) =
      profile.logVolume (applyRoute core route c) := by
  rw [applyRoute_ind1_commute, profile.ind1_invariant]

/-- The output log-volume of the route construction is invariant under the
    (Ind2) action on the input data. -/
theorem applyRoute_ind2_commute_logVolume (core : Core Label Choice)
    (profile : Profile core) (route : List (RouteStep Label))
    (g : Label) (c : Choice) :
    profile.logVolume (applyRoute core route (core.ind2 g c)) =
      profile.logVolume (applyRoute core route c) := by
  rw [applyRoute_ind2_commute, profile.ind2_invariant]

end CommutativeLabels

section GeneralLabels

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- (Ind3) functoriality: the route construction commutes with the log-link
    action.  Paper: IUT III, Theorem 3.11, (ii) (upper-semi compatibility
    (Ind3); the one-sided level law is `Core.ind3_level`). -/
theorem applyRoute_ind3_commute (core : Core Label Choice)
    (route : List (RouteStep Label)) (n : Nat) (c : Choice) :
    applyRoute core route (core.ind3 n c) =
      core.ind3 n (applyRoute core route c) := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          change applyRoute core rest (core.ind1 g (core.ind3 n c)) =
            core.ind3 n (applyRoute core rest (core.ind1 g c))
          rw [core.ind1_ind3_commute g n c]
          exact ih (core.ind1 g c)
      | ind2 g =>
          change applyRoute core rest (core.ind2 g (core.ind3 n c)) =
            core.ind3 n (applyRoute core rest (core.ind2 g c))
          rw [core.ind2_ind3_commute g n c]
          exact ih (core.ind2 g c)
      | ind3 m =>
          change applyRoute core rest (core.ind3 m (core.ind3 n c)) =
            core.ind3 n (applyRoute core rest (core.ind3 m c))
          have hstep : core.ind3 m (core.ind3 n c) =
              core.ind3 n (core.ind3 m c) := by
            rw [← core.ind3_add n m c, ← core.ind3_add m n c,
              Nat.add_comm m n]
          rw [hstep]
          exact ih (core.ind3 m c)

/-- The output log-volume is upper-semi compatible with the (Ind3) log-link
    action, in the direction of the paper's inclusions. -/
theorem applyRoute_ind3_commute_logVolume_le (core : Core Label Choice)
    (profile : Profile core) (route : List (RouteStep Label))
    (n : Nat) (c : Choice) :
    profile.logVolume (applyRoute core route c) ≤
      profile.logVolume (applyRoute core route (core.ind3 n c)) := by
  rw [applyRoute_ind3_commute]
  exact profile.ind3_upper n (applyRoute core route c)

/-- Quotient descent: for a horizontal route (no log-link steps), the output
    class in the indeterminacy quotient equals the input class.  Paper: this
    is the quotient form of the invariance of the multiradial data under
    (Ind1)/(Ind2) (Theorem 3.11, (i)). -/
theorem applyRoute_horizontal_quotient_eq (core : Core Label Choice)
    (route : List (RouteStep Label))
    (hroute : ∀ step ∈ route, horizontal step) (c : Choice) :
    Core.generatedQuotientMap core (applyRoute core route c) =
      Core.generatedQuotientMap core c :=
  (Core.generatedQuotientMap_eq_of_generated core
    (generated_of_horizontal_route core route hroute c)).symm

end GeneralLabels

/-! ## 2. The algorithm contract at the carrier level

  The frozen form of `IUT-III.multiradial-algorithm` at the carrier
  interface: for every input (source point plus route in the procession),
  the algorithm `runAlgorithm` returns an output whose target is the route
  target and whose invariants (level monotone, log-volume monotone, possible
  image upper bound) hold.  Paper: IUT III, Theorem 3.11, (i) (algorithm in
  the procession) with (Ind3) rendered as the image upper bound. -/

section CarrierLevel

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- The carrier-level algorithm contract: totality of `runAlgorithm`
    together with its four output invariants.  This is a reduced form: it
    quantifies over an arbitrary `Carrier`, not over the actual IUT I-II
    data. -/
def CarrierAlgorithmContract
    (carrier : ParametricTheorem311.Carrier Label Choice) : Prop :=
  ∀ input : ParametricTheorem311.AlgorithmInput carrier,
    (ParametricTheorem311.runAlgorithm carrier input).target =
        ParametricTheorem311.algorithmTarget carrier input ∧
      carrier.core.level input.source ≤
        carrier.core.level (ParametricTheorem311.runAlgorithm carrier input).target ∧
      carrier.profile.logVolume input.source ≤
        carrier.profile.logVolume (ParametricTheorem311.runAlgorithm carrier input).target ∧
      (∀ z, z ∈ carrier.profile.possibleImage input.source →
        ∃ w, w ∈ carrier.profile.possibleImage
          (ParametricTheorem311.runAlgorithm carrier input).target ∧ z ≤ w)

/-- The algorithm contract holds for every carrier.  This is the
    unconditional half of the reduction: the residual condition of
    `IUT-III.multiradial-algorithm` is the carrier instance itself. -/
theorem carrierAlgorithmContract
    (carrier : ParametricTheorem311.Carrier Label Choice) :
    CarrierAlgorithmContract carrier := by
  intro input
  exact
    ⟨ParametricTheorem311.runAlgorithm_target carrier input,
      ParametricTheorem311.runAlgorithm_level carrier input,
      ParametricTheorem311.runAlgorithm_profile carrier input,
      fun z hz => ParametricTheorem311.runAlgorithm_image carrier input z hz⟩

/-- The route normal form obligation: every route from the base point can be
    normalized to a log-link lift of a same-level representative.  Paper:
    this is the structural form of "an algorithm in the procession of
    D-prime-strips" (Theorem 3.11, (i), final paragraph) as used by the
    Corollary 3.12 wall.  It is a field of `SourceProcessionBoundary.Input`
    and is proved below for the finite carrier; the general case is open. -/
def RouteNormalForm
    (carrier : ParametricTheorem311.Carrier Label Choice) : Prop :=
  ∀ route : List (RouteStep Label),
    ∃ b n, carrier.core.level b = carrier.core.level carrier.core.base ∧
      ParametricTheorem311.routeTarget carrier route carrier.core.base =
        carrier.core.ind3 n b

/-- Horizontal steps give quotient equality of the algorithm output with the
    algorithm input (the carrier-level form of
    `applyRoute_horizontal_quotient_eq` composed with `runAlgorithm`). -/
theorem algorithmRun_horizontal_quotient
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (hroute : ParametricTheorem311.horizontalRoute carrier input.route) :
    Core.generatedQuotientMap carrier.core
        (ParametricTheorem311.runAlgorithm carrier input).target =
      Core.generatedQuotientMap carrier.core input.source := by
  rw [ParametricTheorem311.runAlgorithm_target,
    ParametricTheorem311.algorithmTarget, ParametricTheorem311.routeTarget]
  exact (Core.generatedQuotientMap_eq_of_generated carrier.core
    (generated_of_horizontal_route carrier.core input.route hroute
      input.source)).symm

/-- (Ind3) upper-semi law for the algorithm: the output image of the input
    is dominated by the output image after a log-link step.  Paper: IUT III,
    Theorem 3.11, (ii) ((Ind3), upper-semi compatibility). -/
theorem algorithmRun_ind3_upper
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (n : Nat) (z : Real)
    (hz : z ∈ carrier.profile.possibleImage input.source) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (carrier.core.ind3 n
        (ParametricTheorem311.runAlgorithm carrier input).target) ∧ z ≤ w := by
  obtain ⟨w₁, hw₁, hzw₁⟩ :=
    ParametricTheorem311.runAlgorithm_image carrier input z hz
  obtain ⟨w₂, hw₂, h₁₂⟩ := carrier.profile.possibleImage_ind3 n
    (ParametricTheorem311.runAlgorithm carrier input).target w₁ hw₁
  exact ⟨w₂, hw₂, hzw₁.trans h₁₂⟩

end CarrierLevel

/-! ## 3. Finite Q(i)-at-5 discharge

  The single concrete carrier of the repository is the Q(i)-at-5 procession
  `SourceFiniteParameterized.carrier`.  For this carrier the route normal
  form is proved (via `ConcreteRouteNormalForm`), and the Ind1/Ind2/Ind3
  laws at the quotient are proved in `SourceFiniteMultiradial`.  The bundle
  below packages exactly these facts.  Boundary: this is one finite model,
  not the general source carrier. -/

section FiniteDischarge

/-- The finite-carrier discharge of the Ind1/Ind2/Ind3 laws at the
    indeterminacy quotient (paper: Theorem 3.11, (i), (Ind1), (Ind2) and
    (ii), (Ind3)). -/
structure FiniteIndeterminacyDischarge (l : PrimeGeFive) : Prop where
  sameLevel_quotient :
    ∀ (a b : ConcreteFiniteTheorem311.ProcessionChoice l),
      a.upperSemiLevel = b.upperSemiLevel →
        Core.generatedQuotientMap (SourceFiniteMultiradial.core l) a =
          Core.generatedQuotientMap (SourceFiniteMultiradial.core l) b
  level_separation :
    ∀ (a b : ConcreteFiniteTheorem311.ProcessionChoice l),
      a.upperSemiLevel ≠ b.upperSemiLevel →
        Core.generatedQuotientMap (SourceFiniteMultiradial.core l) a ≠
          Core.generatedQuotientMap (SourceFiniteMultiradial.core l) b
  sameLevel_volume :
    ∀ (a b : ConcreteFiniteTheorem311.ProcessionChoice l),
      a.upperSemiLevel = b.upperSemiLevel →
        (SourceFiniteMultiradial.profile l).logVolume a =
          (SourceFiniteMultiradial.profile l).logVolume b
  sameLevel_image :
    ∀ (a b : ConcreteFiniteTheorem311.ProcessionChoice l),
      a.upperSemiLevel = b.upperSemiLevel →
        (SourceFiniteMultiradial.profile l).possibleImage a =
          (SourceFiniteMultiradial.profile l).possibleImage b
  quotient_image_nonempty :
    ∀ q : Core.GeneratedQuotient (SourceFiniteMultiradial.core l),
      ((SourceFiniteMultiradial.profile l).quotientPossibleImage q).Nonempty
  quotient_image_ind3_upper :
    ∀ (a : ConcreteFiniteTheorem311.ProcessionChoice l) (n : Nat)
      (z : Real),
      z ∈ (SourceFiniteMultiradial.profile l).quotientPossibleImage
        (Core.generatedQuotientMap (SourceFiniteMultiradial.core l) a) →
      ∃ w, w ∈ (SourceFiniteMultiradial.profile l).quotientPossibleImage
        (Core.generatedQuotientMap (SourceFiniteMultiradial.core l)
          ((SourceFiniteMultiradial.core l).ind3 n a)) ∧ z ≤ w

/-- The finite Q(i)-at-5 carrier satisfies the Ind1/Ind2/Ind3 quotient laws.
    Extraction from `SourceFiniteMultiradial`. -/
theorem finiteIndeterminacyDischarge (l : PrimeGeFive) :
    FiniteIndeterminacyDischarge l where
  sameLevel_quotient := by
    intro a b hlevel
    exact SourceFiniteMultiradial.sameLevel_quotient_eq hlevel
  level_separation := by
    intro a b hlevel
    exact SourceFiniteMultiradial.differentLevel_quotient_ne hlevel
  sameLevel_volume := by
    intro a b hlevel
    exact SourceFiniteMultiradial.sameLevel_logVolume_eq hlevel
  sameLevel_image := by
    intro a b hlevel
    exact SourceFiniteMultiradial.sameLevel_image_eq hlevel
  quotient_image_nonempty := by
    intro q
    exact SourceFiniteMultiradial.quotient_image_nonempty l q
  quotient_image_ind3_upper := by
    intro a n z hz
    exact SourceFiniteMultiradial.quotient_image_ind3_upper a n z hz

/-- The finite carrier satisfies the route normal form.  Extraction from the
    packaged `concreteInput`, whose normal-form field is proved by
    `ConcreteRouteNormalForm`. -/
theorem routeNormalForm_finite (l : PrimeGeFive) :
    RouteNormalForm (SourceFiniteParameterized.carrier l) :=
  (SourceProcessionBoundary.Input.concreteInput l).route_normal_form

/-- For the finite carrier, the algorithm's output for every route is a
    log-link lift of a same-level representative of the base. -/
theorem finiteAlgorithmTarget_normalizes (l : PrimeGeFive)
    (route : List (RouteStep (ConcreteFiniteTheorem311.finiteLabel l))) :
    ∃ b n, (SourceFiniteParameterized.carrier l).core.level b =
        (SourceFiniteParameterized.carrier l).core.level
          (SourceFiniteParameterized.carrier l).core.base ∧
      (ParametricTheorem311.runAlgorithm (SourceFiniteParameterized.carrier l)
          (SourceFiniteParameterized.finiteAlgorithmInput l
            ConcreteFiniteTheorem311.ProcessionChoice.base route)).target =
        (SourceFiniteParameterized.carrier l).core.ind3 n b := by
  obtain ⟨b, n, hlevel, htarget⟩ := routeNormalForm_finite l route
  exact ⟨b, n, hlevel, htarget⟩

/-- The finite Q(i)-at-5 discharge bundle: algorithm contract + route normal
    form + Ind1/Ind2/Ind3 quotient laws, for the single concrete carrier. -/
theorem finiteMultiradialAlgorithmDischarge (l : PrimeGeFive) :
    CarrierAlgorithmContract (SourceFiniteParameterized.carrier l) ∧
      RouteNormalForm (SourceFiniteParameterized.carrier l) ∧
      FiniteIndeterminacyDischarge l :=
  ⟨carrierAlgorithmContract _, routeNormalForm_finite l,
    finiteIndeterminacyDischarge l⟩

end FiniteDischarge

/-! ## 4. Source-level output law bundle and conditional discharge

  Paper: IUT III, Theorem 3.11, (i)-(iii).  The source-facing output record
  `Theorem311Source.Theorem311Output` is already proved from the explicit
  prerequisite package `Theorem311Source.Input` (the repo rendering of the
  cited IUT I-II constructions: initial Theta-data, procession of
  D-prime-strips, packet and log-volume data, vertical upper-semi data,
  labelled Kummer isomorphisms, evaluation system, horizontal LGP link).
  The bundle below freezes the field-level laws that the output must satisfy,
  with each field traced to the declaration that supplies it in
  `SourceFaithfulBoundary.lean`. -/

section SourceLevel

variable {Label : Type u} {Choice' : Type v} [AddGroup Label] [Preorder Choice']

/-- Field-level law bundle of the multiradial output over the explicit source
    prerequisites.  `O` is the output object; every field is supplied by an
    existing proved declaration listed in the doc comments of the extraction
    theorem `theorem311Output_sourceLawBundle`. -/
structure SourceOutputLawBundle
    (I : Theorem311Source.Input Label Choice')
    (O : Theorem311Source.Theorem311Output I) : Prop where
  /-- The source point is the base of the procession.  Supplied by
      `theorem311Output_source`. -/
  source_eq_base : O.source = I.core.base
  /-- Part (i) of the output: the multiradial representation.  Supplied by
      `theorem311Output_part_i`.  Paper: Theorem 3.11, (i). -/
  partI_recovered : O.part_i = Theorem311Source.partI I
  /-- Part (ii): the log-Kummer correspondence.  Supplied by
      `theorem311Output_part_ii`.  Paper: Theorem 3.11, (ii). -/
  partII_recovered : O.part_ii = Theorem311Source.partII I
  /-- Part (iii): Theta-times-mu-link compatibility.  Supplied by
      `theorem311Output_part_iii`.  Paper: Theorem 3.11, (iii). -/
  partIII_recovered : O.part_iii = Theorem311Source.partIII I
  /-- The quotient is the quotient map of the source.  Supplied by
      `theorem311Output_quotient`. -/
  quotient_eq_map :
    O.quotient = Theorem311Source.quotientMap I O.source
  /-- The labelled Kummer maps are bijective.  Supplied by
      `theorem311Output_labelled`. -/
  labelled_bijective :
    ∀ c, Function.Bijective (I.labelledKummer c).map
  /-- (Ind1) descent: the output class is invariant under the procession
      automorphism relation.  Supplied by `theorem311Output_ind1`.
      Paper: Theorem 3.11, (i), (Ind1). -/
  ind1_descent :
    ∀ {a b : Choice'}, Theorem311Source.Ind1Relation I a b →
      Theorem311Source.quotientMap I a = Theorem311Source.quotientMap I b
  /-- (Ind2) descent.  Supplied by `theorem311Output_ind2`.
      Paper: Theorem 3.11, (i), (Ind2). -/
  ind2_descent :
    ∀ {a b : Choice'}, Theorem311Source.Ind2Relation I a b →
      Theorem311Source.quotientMap I a = Theorem311Source.quotientMap I b
  /-- (Ind3) upper-semi bound.  Supplied by `theorem311Output_ind3`.
      Paper: Theorem 3.11, (ii), (Ind3). -/
  ind3_upper :
    ∀ n (c : Choice') (z : Real),
      z ∈ I.profile.possibleImage c →
        ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 n c) ∧ z ≤ w
  /-- Horizontal square of the LGP link.  Supplied by
      `theorem311Output_horizontal`.  Paper: Theorem 3.11, (iii). -/
  horizontal_square :
    ∀ c, I.horizontal.upper (I.horizontal.left c) =
      I.horizontal.right (I.horizontal.lower c)
  /-- Evaluation compatibility.  Supplied by
      `theorem311Output_evaluation`.  Paper: Theorem 3.11, (iii), (c), (d). -/
  evaluation_square :
    ∀ c, I.evaluation.localMap (I.horizontal.left c) =
      I.horizontal.right (I.evaluation.localMap (I.horizontal.lower c))

/-- Extraction: the assembled output satisfies the frozen law bundle.
    Every field is a projection of a theorem already proved in
    `SourceFaithfulBoundary.lean`; this theorem introduces no new
    mathematical content, only the frozen consumer-facing interface. -/
theorem theorem311Output_sourceLawBundle
    (I : Theorem311Source.Input Label Choice') :
    SourceOutputLawBundle I (Theorem311Source.theorem311Output I) where
  source_eq_base := Theorem311Source.theorem311Output_source I
  partI_recovered := Theorem311Source.theorem311Output_part_i I
  partII_recovered := Theorem311Source.theorem311Output_part_ii I
  partIII_recovered := Theorem311Source.theorem311Output_part_iii I
  quotient_eq_map := Theorem311Source.theorem311Output_quotient I
  labelled_bijective := fun c => Theorem311Source.theorem311Output_labelled I c
  ind1_descent := fun h => Theorem311Source.theorem311Output_ind1 I h
  ind2_descent := fun h => Theorem311Source.theorem311Output_ind2 I h
  ind3_upper := fun n c z hz => Theorem311Source.theorem311Output_ind3 I n c z hz
  horizontal_square := fun c => Theorem311Source.theorem311Output_horizontal I c
  evaluation_square := fun c => Theorem311Source.theorem311Output_evaluation I c

/-- Conditional discharge of `IUT-III.theorem-3.11-output`: the multiradial
    output with all field-level laws exists whenever the explicit source
    prerequisite package `Theorem311Source.Input` is supplied.  The package
    is a parameter, not a construction: instantiating it from the actual
    IUT I-II data remains the open card recorded at the end of this file. -/
theorem sourceMultiradialOutputDischarge
    (I : Theorem311Source.Input Label Choice') :
    ∃ O : Theorem311Source.Theorem311Output I,
      SourceOutputLawBundle I O :=
  ⟨Theorem311Source.theorem311Output I,
    theorem311Output_sourceLawBundle I⟩

end SourceLevel

end MultiradialAlgorithmReduction

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Reduction record for `IUT-III.theorem-3.11-output`.  Conditional: the
    output and its field-level laws are proved from the explicit prerequisite
    package; constructing that package from the actual IUT I-II data is not
    done here. -/
def multiradialOutputReductionRecord : Obligation :=
  { id := "IUT-III.theorem-3.11-output.reduction"
    source := "IUT III, Theorem 3.11, (i) (multiradial representation)"
    status := VerificationStatus.conditional
    note :=
      "Proved: `theorem311Output_sourceLawBundle` and " ++
        "`sourceMultiradialOutputDischarge` (the assembled output satisfies " ++
        "the frozen field-level laws: source/quotient/part recovery, " ++
        "labelled Kummer bijectivity, Ind1/Ind2 descent, Ind3 upper-semi, " ++
        "horizontal and evaluation squares).  Remaining card: instantiate " ++
        "`Theorem311Source.Input` from the actual IUT I-II constructions " ++
        "(initial Theta-data, D-prime-strip procession, packet and " ++
        "log-volume data, vertical log-Kummer boundary, labelled Kummer, " ++
        "evaluation, horizontal link).  The finite Q(i)-at-5 carrier is not " ++
        "the general source carrier.  No extra unfounded assumption is added."
    dependsOn :=
      [ "IUT-III.theorem-3.11-explicit-prerequisite-boundary",
        "IUT-III.concrete-source-theorem311-output",
        "IUT-I.initial-theta-data",
        "IUT-I-II.prime-strips-frobenioids",
        "IUT-II.vertical-log-kummer" ]
    }

/-- Reduction record for `IUT-III.multiradial-algorithm`.  Conditional:
    the algorithm interface and its invariants are proved unconditionally at
    the carrier level (with the (Ind1)/(Ind2) functoriality for commutative
    label groups) and for the finite carrier; the carrier instance from the
    actual data and the general route normal form remain open. -/
def multiradialAlgorithmReductionRecord : Obligation :=
  { id := "IUT-III.multiradial-algorithm.reduction"
    source := "IUT III, Theorem 3.11, (i) (algorithm in the procession; " ++
      "functoriality); (ii) ((Ind3))"
    status := VerificationStatus.conditional
    note :=
      "Proved unconditionally at the carrier level: `carrierAlgorithmContract` " ++
        "(totality of `runAlgorithm` with target/level/volume/image " ++
        "invariants), `algorithmRun_horizontal_quotient`, " ++
        "`algorithmRun_ind3_upper`, and kernel functoriality under the " ++
        "(Ind1)/(Ind2) actions for commutative label groups and the (Ind3) " ++
        "action in general (`applyRoute_ind1_commute`, " ++
        "`applyRoute_ind2_commute`, `applyRoute_ind3_commute` with " ++
        "log-volume corollaries).  Proved for the finite Q(i)-at-5 carrier: " ++
        "`finiteMultiradialAlgorithmDischarge` (algorithm contract + route " ++
        "normal form + Ind1/Ind2/Ind3 quotient laws).  Remaining cards: " ++
        "(1) carrier instance from the actual IUT I-II data (connector and " ++
        "level-additivity); (2) general route normal form beyond the finite " ++
        "carrier.  Neither card is claimed."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output",
        "IUT-III.concrete-source-multiradial-kernel",
        "IUT-III.parametric-D-stage-certificates",
        "IUT-III.concrete-route-normal-form" ]
    }

end LeanFormal.IUT.Audit
