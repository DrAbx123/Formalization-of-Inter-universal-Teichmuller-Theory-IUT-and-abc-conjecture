import LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Card-IPL conditional assembly path: kernel-level poly-isomorphism transport laws

This module solidifies the conditional assembly path of the Card-IPL G1
verdict (`tmp/outsider-survey-transport-20261016/ProbeCardIPLG1Verdict.lean`,
SHA256 `D660C2B40E5332E62769CC93C6F5E4721A3B7240A960ADCBA40B6069BF4B02AD`;
report `logs/coordination/outsider-survey-transport-20261016.md`, section 15)
into a consumable `LeanFormal` module, as the next step after the G1 judgment.
The two negative results of the verdict (the shell alone does not determine
the times-mu carrier or the poly-isomorphism layer) are relied on as recorded
history and are NOT re-proved here.  What is frozen here:

1. the link shell `LinkSpan` -- the R4 span-lite reduction, re-housed with
   identical fields and statements;
2. the named supply structure `CardIPLTransportSupply` -- the O1--O4
   obligation list of the G1 verdict (report section 15.2).  The fields are
   discharge obligations; no source instantiation is constructed or asserted;
3. the transport-relation-level laws: given a supply `E` over a shell `L`, the
   shell's two-route (SHE-shaped) laws upgrade to the poly-isomorphism-
   transported relation `polyIsoRel L E` (the exchange laws
   `polyIsoRel_ind1_iff` / `polyIsoRel_ind2_iff`, diagonal synchronization,
   the route form, and the identity-poly-isomorphism collapse);
4. the consumer interface `CardIPLExchangeShape` -- the Corollary 3.12 Step
   (xi-b)/(xi-c) exchange shape as a frozen law bundle.

## Original (paper) route

* IUT III, Remark 3.11.1, (iii) (pagewise:9850--9865, 9869--9878): the output
  data "is linked/related, via full poly-isomorphisms of F-prime-strips
  induced by operations in the algorithm, to the input data prime-strip,
  i.e., the coric/fixed q-pilot prime-strip"; the linking isomorphisms of the
  intermediate prime-strips are given by composing the inverses of the first
  two lower horizontal arrows, followed by the first vertical arrow
  (Kummer theory portion), followed by the upper horizontal arrows
  (evaluation map portion).
* IUT III, Remark 3.11.1, (iv): (APT) (pagewise:9931--9938) -- the parallel
  transport "does not consist of a simple instance of transport of some
  set-theoretic region ... via some set-theoretic function.  Rather, it
  consists of a construction algorithm that is simultaneously
  valid/executable/well-defined with respect to the arithmetic holomorphic
  structures in the domain and codomain of the Theta-link"; (HIS)
  (pagewise:9947--9958) -- for the qualitative logical consequences one may
  regard the algorithm as producing "some sort of output data" from "some
  sort of input data" and forget theta functions/values.
* IUT III, Corollary 3.12, proof, Step (xi-b) (pagewise:10950 seqq.; focused
  extract `IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.plain.txt` under
  `papers/motizuki_corpus/text/source_audit/`,
  lines 1007--1044, the property list at 1032--1034): the properties consumed
  are (IPL), (SHE), (APT); the F-prime-strip portion of the link "consists
  precisely of (full poly-)isomorphisms of F-prime-strips", while the
  corresponding link for the F-times-mu prime-strips is complicated by the
  indeterminacies (Ind1), (Ind2), (Ind3).
* IUT III, Corollary 3.12, proof, Step (xi-c) (focused extract lines
  1045--1066): summary -- the algorithm yields output possibilities linked
  [cf. (IPL)] via isomorphisms of F-prime-strips to the representation of the
  q-pilot object, and constructible relative to the arithmetic holomorphic
  structure in the 1-column [cf. (SHE)].

## Reduced route (deviations; inherited from the G1 verdict, unchanged)

R1. Kernel level: the shell links two output kernels `Core Label Choice` of
    the frozen `MultiradialOutputKernel.lean`
    (SHA256 `5538016E...`); the paper's prime strips and Theta-link carriers
    are not constructed.
R2. Shell: `LinkSpan` is the R4 span-lite reduction (carrier, two legs, two
    commuting label actions, level compatibility).  No procession transition
    structure, no automorphism action on a procession, no (Ind3) action: the
    shell carries the two invertible label actions only, and the
    (Ind3)/upper-semi layer is out of scope (same exclusion as R4).
R3. Supply: `CardIPLTransportSupply` repeats the O1--O4 obligations exactly as
    frozen in G1 verdict section 15.2 (same fields, same strength).  The
    paper's multiplicities x2/x3 and the multiplicative display of the
    times-mu layer are not modelled (same reductions as the verdict).
R4. The transport laws are conditional on the supply: no field of the supply
    is constructed from the shell (impossible by the verdict's negative
    results) or from source data.  In particular, the (xi-b) sentence that
    the isomorphism "arises from the permutation symmetries discussed in the
    final portion of Theorem 3.11, (i)" is carried as the provenance field
    and is NOT constructed; its source discharge requires the full
    poly-isomorphism object (API-1) and the adjacent-column comparison
    square (API-2) of `SourceFTimesMuPrimeStripPolyIsomorphism.lean`
    (SHA256 `12F25145...`, in flight; the Volta-branch dependency is
    documented in the module docstring below).

## Alignment with the source-level cards (API-4)

The supply field shapes mirror the data faces frozen (read-only) in
`LeanFormal/IUT/IUTIII/Theorem311/SourceMultiradialTwoActionEquivalence.lean`
(SHA256 `DE0B8E1C466690BFE15981949D815AA8E1A6938A9BA5C44B315AD59AFB040553`):

* O2 (`polyIso`, `polyIso_act1`, `polyIso_act2`) is the reduced shape of Card
  TA, `SourceTheorem311TwoActionEquivalence.{outputEquiv, preserves_ind1,
  preserves_ind2}`: a carrier equivalence preserving both actions, with the
  (Ind1) group identification collapsed to the shared label group acting
  diagonally on both sides.
* O4 (`kummerEval` with its two factorization laws) is the reduced shape of
  Card U2P, `SourceSquareUnitLayerTwoPath.coherence`: each factorization law
  is the equality of the two composites of one half of the Kummer-evaluation
  square at the reduced shell level.
* O1's times-mu carrier is the reduced shadow of the per-place unit-layer
  torsion quotients `TimesMuQuotient ((S.Mon v)ˣ)` and the family action
  `unitLayerFamilyAction` of API-3/API-4; the source-level carrier is
  `SourceFTimesMuPrimeStrip.timesMu` (the times-mu prime-strip module, in
  flight).

No type-level bridge from the API-3/API-4/API-5 source records to this
kernel-level shell is constructed here; that bridge is exactly the open
source instantiation, and this module does not import the source chain.

## Open obligations (no free construction)

* Every supply field is a hypothesis.  Discharging O2/O3 from source data
  requires the full poly-isomorphism object of the times-mu prime-strips
  (API-1) and the adjacent-column comparison square (API-2) of the times-mu
  prime-strip module (in flight; Volta branch).  This module imports none of
  these files.
* No relation-level transport law for the O4 Kummer step is stated: the
  frozen supply contains no poly-isomorphism/Kummer compatibility field, and
  adding one would strengthen the obligation list (left to a future card).
* (Ind3) transport is out of scope of the shell (R2).
* The two G1 negative results are relied on as recorded history (probe SHA
  above), not re-proved; no new negative result is claimed here.

## Proved here

Shell laws (`LinkSpan.rel_ind1_iff`, `LinkSpan.rel_ind2_iff`,
`LinkSpan.refl`); the transported relation `polyIsoRel` with diagonal
synchronization, the two exchange laws, the route form, and the identity
collapse; and the exchange-shape bundle `CardIPLExchangeShape` with its
constructor from a supply.

## Non-claims

No construction of the paper's prime strips, of the times-mu layer, or of the
full poly-isomorphism object; no assertion that any source instantiation
satisfies O1--O4; no IPL/SHE/APT conclusion.  The transfer laws are
conditional on the named supply; they generalize the shell's two-route laws
(see `polyIsoRel_eq_rel_of_polyIso_refl`) and do not replace them.
-/

namespace LeanFormal.IUT

namespace Theorem311Source

namespace PolyIsoTransport

open LeanFormal.IUT.MultiradialKernel

universe u v w z

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-! ## 1. The reduced R4 link shell (re-housed with identical statements) -/

/-- Cancellation in the orientation not stored in the kernel: the kernel has
`ind1 (-g) (ind1 g c) = c`; this is the other order.  (Identical statement to
the R4 shell's `ind1_inv_cancel`.) -/
theorem ind1_inv_cancel (core : Core Label Choice) (g : Label) (c : Choice) :
    core.ind1 g (core.ind1 (-g) c) = c := by
  calc core.ind1 g (core.ind1 (-g) c)
      = core.ind1 ((-g) + g) c := (core.ind1_add (-g) g c).symm
    _ = core.ind1 0 c := by rw [neg_add_cancel]
    _ = c := core.ind1_zero c

/-- Cancellation in the orientation not stored in the kernel, for (Ind2).
(Identical statement to the R4 shell's `ind2_inv_cancel`.) -/
theorem ind2_inv_cancel (core : Core Label Choice) (g : Label) (c : Choice) :
    core.ind2 g (core.ind2 (-g) c) = c := by
  calc core.ind2 g (core.ind2 (-g) c)
      = core.ind2 ((-g) + g) c := (core.ind2_add (-g) g c).symm
    _ = core.ind2 0 c := by rw [neg_add_cancel]
    _ = c := core.ind2_zero c

/-- A link span between two kernels (the R4 span-lite shell): a carrier with
two legs into the shared `Choice` type, two commuting label actions on the
carrier that transport the two cores' (Ind1)/(Ind2) actions along both legs,
and a level function compatible with both cores' levels.  This is the lite
gluing object of the Theta-link/(Ind1)/(Ind2) chain; every field is an
explicit obligation a source instantiation must discharge, and no source link
is asserted to satisfy them.  (Identical fields and statements to the R4
shell's `LinkSpan`.) -/
structure LinkSpan (core1 : Core Label Choice) (core2 : Core Label Choice) where
  mid : Type w
  left : mid → Choice
  right : mid → Choice
  act1 : Label → mid → mid
  act1_zero : ∀ m, act1 0 m = m
  act1_add : ∀ g h m, act1 (g + h) m = act1 h (act1 g m)
  act2 : Label → mid → mid
  act2_zero : ∀ m, act2 0 m = m
  act2_add : ∀ g h m, act2 (g + h) m = act2 h (act2 g m)
  act12_commute : ∀ g h m, act1 g (act2 h m) = act2 h (act1 g m)
  left_act1 : ∀ g m, left (act1 g m) = core1.ind1 g (left m)
  right_act1 : ∀ g m, right (act1 g m) = core2.ind1 g (right m)
  left_act2 : ∀ g m, left (act2 g m) = core1.ind2 g (left m)
  right_act2 : ∀ g m, right (act2 g m) = core2.ind2 g (right m)
  level : mid → Nat
  level_left : ∀ m, core1.level (left m) = level m
  level_right : ∀ m, core2.level (right m) = level m

namespace LinkSpan

variable {core1 core2 : Core Label Choice}

/-- The relation transported by a link: `a` on the first side and `b` on the
second side are connected through some state of the link carrier. -/
def Rel (L : LinkSpan core1 core2) (a b : Choice) : Prop :=
  ∃ m : L.mid, L.left m = a ∧ L.right m = b

/-- The two-route (SHE-shaped) law for (Ind1): an (Ind1)-step on the first
side corresponds to the inverse step on the second side. -/
theorem rel_ind1_iff (L : LinkSpan core1 core2) (a b : Choice) (g : Label) :
    L.Rel (core1.ind1 g a) b ↔ L.Rel a (core2.ind1 (-g) b) := by
  constructor
  · rintro ⟨m, h1, h2⟩
    refine ⟨L.act1 (-g) m, ?_, ?_⟩
    · rw [L.left_act1, h1, core1.ind1_inverse]
    · rw [L.right_act1, h2]
  · rintro ⟨m, h1, h2⟩
    refine ⟨L.act1 g m, ?_, ?_⟩
    · rw [L.left_act1, h1]
    · rw [L.right_act1, h2, ind1_inv_cancel core2 g b]

/-- The two-route (SHE-shaped) law for (Ind2). -/
theorem rel_ind2_iff (L : LinkSpan core1 core2) (a b : Choice) (g : Label) :
    L.Rel (core1.ind2 g a) b ↔ L.Rel a (core2.ind2 (-g) b) := by
  constructor
  · rintro ⟨m, h1, h2⟩
    refine ⟨L.act2 (-g) m, ?_, ?_⟩
    · rw [L.left_act2, h1, core1.ind2_inverse]
    · rw [L.right_act2, h2]
  · rintro ⟨m, h1, h2⟩
    refine ⟨L.act2 g m, ?_, ?_⟩
    · rw [L.left_act2, h1]
    · rw [L.right_act2, h2, ind2_inv_cancel core2 g b]

/-- The identity link: the carrier is the shared `Choice` type itself. -/
def refl (core : Core Label Choice) : LinkSpan core core where
  mid := Choice
  left := id
  right := id
  act1 := core.ind1
  act1_zero := core.ind1_zero
  act1_add := core.ind1_add
  act2 := core.ind2
  act2_zero := core.ind2_zero
  act2_add := core.ind2_add
  act12_commute := core.ind1_ind2_commute
  left_act1 := fun _ _ => rfl
  right_act1 := fun _ _ => rfl
  left_act2 := fun _ _ => rfl
  right_act2 := fun _ _ => rfl
  level := core.level
  level_left := fun _ => rfl
  level_right := fun _ => rfl

end LinkSpan
/-! ## 2. The Card-IPL supply: the O1--O4 obligation list (G1 verdict 15.2) -/

/-- Reduced provenance evaluator (the O3 reduction): apply a list of label
steps along the (Ind1)-leg of the link carrier.  The real algorithm route is
`List (RouteStep Label)` (`ParametricCarrier.lean`); this lite stand-in is
restricted to (Ind1)-steps, as in the G1 verdict. -/
def routeApply {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (route : List Label) (m : L.mid) : L.mid :=
  route.foldl (fun m g => L.act1 g m) m

/-- O4 of the supply obligation list (reduced): the Remark 3.11.1, (iii)
composite decomposition (inverse lower horizontal, then vertical Kummer, then
upper horizontal) as a factoring of the Kummer step through the two link
legs.  Each factorization law is an equality of two composites -- the reduced
two-path shape of the unit-layer card U2P of API-4
(`SourceSquareUnitLayerTwoPath.coherence`).  The paper's multiplicities x2/x3
are NOT modelled (same reduction as the G1 verdict). -/
structure KummerEvaluationFactor {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) where
  lower : Choice → Choice
  upper : Choice → Choice
  kummer : L.mid → L.mid
  lower_left : ∀ m, L.left (kummer m) = lower (L.left m)
  upper_right : ∀ m, L.right (kummer m) = upper (L.right m)

/-- The Card-IPL supply: the O1--O4 obligation list frozen by the G1 verdict
(report section 15.2; probe `CardIPLG1Realization`), re-housed as a named
supply structure.  Every field is a discharge obligation for an eventual
source instantiation; the obligations are not weakened relative to the G1
verdict, and no source instantiation is asserted.

* O1 `XMu` + `xmuGroup` + `xmuAct` (one/add laws): the times-mu layer as an
  object (the repository has only per-component quotients,
  `IUTII/Kummer/TimesMuQuotient.lean`; the source-level carrier is
  `SourceFTimesMuPrimeStrip.timesMu`, in flight).
* O2 `polyIso` + `polyIso_act1` + `polyIso_act2`: the full poly-isomorphism
  proxy -- a carrier equivalence compatible with both label actions (the
  reduced Card TA shape; see the module docstring for the API-4 alignment).
* O3 `provenance` + `polyIso_eq_provenance`: the poly-isomorphism is induced
  by an algorithm route (reduced to a list of label steps; cf. the composite
  decomposition of Remark 3.11.1, (iii), and the (xi-b) sentence on the
  permutation symmetries).
* O4 `kummerEval`: the reduced Kummer-evaluation factorization (above).

The fields are carried in full even where the transport laws of section 3
consume only O2 (and O3 for the route form): the structure is the frozen
obligation list of the card, not a minimal hypothesis set. -/
structure CardIPLTransportSupply {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) where
  XMu : Type z
  [xmuGroup : AddCommGroup XMu]
  xmuAct : Label → XMu → XMu
  xmuAct_zero : ∀ x, xmuAct 0 x = x
  xmuAct_add : ∀ g h x, xmuAct (g + h) x = xmuAct h (xmuAct g x)
  polyIso : L.mid ≃ L.mid
  polyIso_act1 : ∀ g m, polyIso (L.act1 g m) = L.act1 g (polyIso m)
  polyIso_act2 : ∀ g m, polyIso (L.act2 g m) = L.act2 g (polyIso m)
  provenance : List Label
  polyIso_eq_provenance : ∀ m, polyIso m = routeApply L provenance m
  kummerEval : KummerEvaluationFactor L
/-! ## 3. The transported relation and its laws (given a supply) -/

/-- The relation transported by a link once the second side is read through
the supply's poly-isomorphism: `a` (output side) is connected to `b`
(q-pilot/input side) after the output-to-input identification `E.polyIso`.
This is the reduced shadow of the IPL link of Remark 3.11.1, (iii):
"linked/related, via full poly-isomorphisms ... to the input data
prime-strip". -/
def polyIsoRel {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (E : CardIPLTransportSupply L) (a b : Choice) : Prop :=
  ∃ m : L.mid, L.left m = a ∧ L.right (E.polyIso m) = b

/-- The route form of the transported relation: the second leg is read after
applying the supply's algorithm route (the reduced "induced by operations in
the algorithm" of Remark 3.11.1, (iii)). -/
def routeRel {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (E : CardIPLTransportSupply L) (a b : Choice) : Prop :=
  ∃ m : L.mid, L.left m = a ∧ L.right (routeApply L E.provenance m) = b

/-- The route form presents the same relation: O3 rewrites the
poly-isomorphism to its route fold. -/
theorem polyIsoRel_eq_routeRel {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (E : CardIPLTransportSupply L) (a b : Choice) :
    polyIsoRel L E a b ↔ routeRel L E a b := by
  constructor
  · rintro ⟨m, h1, h2⟩
    exact ⟨m, h1, by rw [← E.polyIso_eq_provenance m]; exact h2⟩
  · rintro ⟨m, h1, h2⟩
    exact ⟨m, h1, by rw [E.polyIso_eq_provenance m]; exact h2⟩

/-- Both sides move together along the poly-isomorphism-transported relation
(diagonal synchronization along (Ind1)). -/
theorem polyIsoRel_act1 {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (E : CardIPLTransportSupply L)
    {a b : Choice} (h : polyIsoRel L E a b) (g : Label) :
    polyIsoRel L E (core1.ind1 g a) (core2.ind1 g b) := by
  rcases h with ⟨m, h1, h2⟩
  exact ⟨L.act1 g m, by rw [L.left_act1, h1],
    by rw [E.polyIso_act1, L.right_act1, h2]⟩

/-- Both sides move together along the poly-isomorphism-transported relation
(diagonal synchronization along (Ind2)). -/
theorem polyIsoRel_act2 {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (E : CardIPLTransportSupply L)
    {a b : Choice} (h : polyIsoRel L E a b) (g : Label) :
    polyIsoRel L E (core1.ind2 g a) (core2.ind2 g b) := by
  rcases h with ⟨m, h1, h2⟩
  exact ⟨L.act2 g m, by rw [L.left_act2, h1],
    by rw [E.polyIso_act2, L.right_act2, h2]⟩

/-- Two-route exchange law for the poly-isomorphism-transported relation (the
Corollary 3.12 Step (xi-b)/(xi-c) exchange shape): an (Ind1)-step on the
output side is equivalent to the inverse (Ind1)-step on the q-pilot side,
after the identification. -/
theorem polyIsoRel_ind1_iff {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (E : CardIPLTransportSupply L)
    (a b : Choice) (g : Label) :
    polyIsoRel L E (core1.ind1 g a) b ↔
      polyIsoRel L E a (core2.ind1 (-g) b) := by
  constructor
  · rintro ⟨m, h1, h2⟩
    refine ⟨L.act1 (-g) m, ?_, ?_⟩
    · rw [L.left_act1, h1, core1.ind1_inverse]
    · rw [E.polyIso_act1, L.right_act1, h2]
  · rintro ⟨m, h1, h2⟩
    refine ⟨L.act1 g m, ?_, ?_⟩
    · rw [L.left_act1, h1]
    · rw [E.polyIso_act1, L.right_act1, h2, ind1_inv_cancel core2 g b]

/-- Two-route exchange law for the poly-isomorphism-transported relation
((Ind2) version). -/
theorem polyIsoRel_ind2_iff {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (E : CardIPLTransportSupply L)
    (a b : Choice) (g : Label) :
    polyIsoRel L E (core1.ind2 g a) b ↔
      polyIsoRel L E a (core2.ind2 (-g) b) := by
  constructor
  · rintro ⟨m, h1, h2⟩
    refine ⟨L.act2 (-g) m, ?_, ?_⟩
    · rw [L.left_act2, h1, core1.ind2_inverse]
    · rw [E.polyIso_act2, L.right_act2, h2]
  · rintro ⟨m, h1, h2⟩
    refine ⟨L.act2 g m, ?_, ?_⟩
    · rw [L.left_act2, h1]
    · rw [E.polyIso_act2, L.right_act2, h2, ind2_inv_cancel core2 g b]

/-- Identity-poly-isomorphism compatibility bridge: for an identity
poly-isomorphism the transported relation is the shell relation itself, so
the transfer laws of this section generalize the shell's two-route laws
rather than replacing them. -/
theorem polyIsoRel_eq_rel_of_polyIso_refl {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (E : CardIPLTransportSupply L)
    (h : E.polyIso = Equiv.refl L.mid) (a b : Choice) :
    polyIsoRel L E a b ↔ L.Rel a b := by
  constructor
  · rintro ⟨m, h1, h2⟩
    rw [h] at h2
    exact ⟨m, h1, h2⟩
  · rintro ⟨m, h1, h2⟩
    exact ⟨m, h1, by rw [h]; exact h2⟩

/-! ## 4. The Corollary 3.12 Step (xi-b)/(xi-c) consumer interface -/

/-- The (xi-b)/(xi-c) exchange shape, frozen as a law bundle over a shell and
a supply: the transported relation is synchronized by both actions
diagonally, one-sided steps exchange against inverse steps on the other side
(the reduced (Ind1)/(Ind2) indeterminacies of the F-times-mu side), the route
form of the link is available, and the identity-poly-isomorphism case
collapses to the shell relation.

Paper anchors: Remark 3.11.1, (iii) (pagewise:9850--9865, 9869--9878);
Remark 3.11.1, (iv) (APT pagewise:9931--9938 -- the transport is not a
set-theoretic function of one side but is valid on both sides simultaneously;
here both exchange laws are proved from the one shared poly-isomorphism
datum); (HIS) (pagewise:9947--9958); Step (xi-b) (focused extract lines
1032--1034); Step (xi-c) (focused extract lines 1045--1066).

This is the frozen shape; a consumer receives it after a source instantiation
supplies a shell and a discharged `CardIPLTransportSupply`.  The source
instantiation itself is the open obligation (module docstring); in particular
the (xi-b) permutation-symmetry identification requires the API-2
adjacent-column square, currently in flight (Volta branch). -/
structure CardIPLExchangeShape {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (E : CardIPLTransportSupply L) where
  /-- (Ind1)-step exchange: one (Ind1)-step on the output side corresponds to
  the inverse (Ind1)-step on the q-pilot side, after the identification. -/
  ind1_step_exchange : ∀ (a b : Choice) (g : Label),
    polyIsoRel L E (core1.ind1 g a) b ↔ polyIsoRel L E a (core2.ind1 (-g) b)
  /-- (Ind2)-step exchange. -/
  ind2_step_exchange : ∀ (a b : Choice) (g : Label),
    polyIsoRel L E (core1.ind2 g a) b ↔ polyIsoRel L E a (core2.ind2 (-g) b)
  /-- Diagonal synchronization along (Ind1). -/
  ind1_diagonal : ∀ (a b : Choice) (g : Label),
    polyIsoRel L E a b → polyIsoRel L E (core1.ind1 g a) (core2.ind1 g b)
  /-- Diagonal synchronization along (Ind2). -/
  ind2_diagonal : ∀ (a b : Choice) (g : Label),
    polyIsoRel L E a b → polyIsoRel L E (core1.ind2 g a) (core2.ind2 g b)
  /-- Route form of the link (the reduced "induced by operations in the
  algorithm"). -/
  route_form : ∀ a b : Choice, polyIsoRel L E a b ↔ routeRel L E a b
  /-- Identity-poly-isomorphism collapse to the shell relation. -/
  refl_collapse : E.polyIso = Equiv.refl L.mid → ∀ a b : Choice,
    polyIsoRel L E a b ↔ L.Rel a b

/-- Constructor: every shell with a supply carries the exchange shape.  This
is the conditional assembly path; the mathematical content of the shape is
carried by the supply's O2/O3 fields, and the remaining obligations of the
supply are not consumed by the shape (they remain to be discharged for the
further cards). -/
theorem cardIPLExchangeShape {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (E : CardIPLTransportSupply L) :
    CardIPLExchangeShape L E where
  ind1_step_exchange := fun a b g => polyIsoRel_ind1_iff L E a b g
  ind2_step_exchange := fun a b g => polyIsoRel_ind2_iff L E a b g
  ind1_diagonal := fun _ _ g h => polyIsoRel_act1 L E h g
  ind2_diagonal := fun _ _ g h => polyIsoRel_act2 L E h g
  route_form := fun a b => polyIsoRel_eq_routeRel L E a b
  refl_collapse := fun h a b => polyIsoRel_eq_rel_of_polyIso_refl L E h a b

end PolyIsoTransport

end Theorem311Source

namespace Audit

/-- The Card-IPL conditional assembly path at the reduced kernel level:
transport-relation laws conditional on the named supply, with the frozen
Corollary 3.12 Step (xi-b)/(xi-c) exchange shape. -/
def cardIPLPolyIsoTransportLaws : Obligation :=
  { id := "IUT-III.card-ipl-poly-iso-transport-laws"
    source :=
      "IUT III, Remark 3.11.1, (iii) (IPL; composite decomposition), (iv) " ++
        "(APT, HIS); Corollary 3.12, proof, Step (xi-b), (xi-c)"
    status := VerificationStatus.interface
    note :=
      "Reduced kernel-level transport laws for the Card-IPL conditional " ++
        "assembly path (G1 verdict, report section 15): re-housed shell " ++
        "`LinkSpan`; supply `CardIPLTransportSupply` (O1--O4 obligation " ++
        "list, fields as hypotheses); transported relation `polyIsoRel` " ++
        "with diagonal synchronization, the (Ind1)/(Ind2) exchange laws, " ++
        "the route form, and the identity collapse; and the frozen " ++
        "exchange-shape bundle `CardIPLExchangeShape`.  The G1 negative " ++
        "results are relied on as recorded history, not re-proved.  " ++
        "Discharging O2/O3 from source data requires the full " ++
        "poly-isomorphism object (API-1) and the adjacent-column comparison " ++
        "square (API-2) of the times-mu prime-strip module, currently in " ++
        "flight; no source instantiation is constructed."
    dependsOn :=
      [ "IUT-III.source-multiradial-two-action-equivalence",
        "IUT-III.source-kummer-evaluation-arrows",
        "IUT-III.source-ftimes-mu-prime-strip-poly-isomorphism" ] }

end Audit

end LeanFormal.IUT
