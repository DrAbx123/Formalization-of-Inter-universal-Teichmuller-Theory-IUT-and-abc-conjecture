import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Realization
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2ValueMapEntry
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteOutputLawBundleVerticalWiring
import Mathlib.Tactic

/-!
  # K1/K2 comparison four-alignments and the global finite-model link
  (run k1k2-realization-20261016, continuation package)

  The K2 boundary record `K2FrobenioidBoundary` (item 28) carries four
  alignment equations between its comparison package and the evaluation slice
  of the frozen realization `R`:

  `comparison.localMap = R.evaluation.evaluation.localMap`, and the global,
  lower (`localComp`) and upper (`globalComp`) variants
  (`SourceK1K2Construction.lean:375-383`).  This file discharges all four
  from a single hypothesis:

  * `identityComparison`: the canonical comparison package on one index type
    (all four structure maps are `id`, all laws are definitional).
  * `identityComparison_alignments_of_evaluation_eq_identity`: if the frozen
    evaluation slice is `SourceOutputWiring.identityEvaluationSystem Choice`
    (as it is by construction for the canonical evaluation bridge
    `sourceEvaluationBridgeOfVertical`), the four alignments hold
    definitionally.
  * `k2FrobenioidBoundaryOfIdentityEvaluation` and
    `k2FrobenioidBoundary_nonempty_of_identityEvaluation`: the K2 record from
    any link layer `L`, conditional only on that single evaluation equation.

  Global existence of the finite-model link layer:
  `finitePlaceSelfLinkLayer` constructs a `PrimeStripFrobenioidLinkLayer` on
  the *global* carrier `FinitePlaceValueFamily s` from the total-degree value
  map (through `primeStripFrobenioidLinkLayerOfValueMaps`,
  `SourceK1K2ValueMapEntry.lean`), and
  `k2FrobenioidBoundary_nonempty_of_finitePlaceSelfLink` inhabits the K2
  record over the global carrier.  This is a self-link (local and global
  carrier are the same family); it does *not* supply the source's
  local-to-global arithmetic `MOD` direction, which remains Card MD2
  (`PrimeStripsFrobenioidLinks.lean`, `MODDirectionCard`).
-/

set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe u v ux uy

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. Canonical comparison and the four alignments -/

/-- The canonical `SourceProposition310Comparison` on a single index type: all
four maps are `id`, the labelled pair is the identity with constant zero
label, and every law holds definitionally. -/
def identityComparison (A : Type u) : SourceProposition310Comparison A A where
  localMap := id
  globalMap := id
  localEqGlobal := fun _ => rfl
  lower := id
  upper := id
  square := fun _ => rfl
  labelledMap := id
  labelledInverse := id
  labelledLeft := fun _ => rfl
  labelledRight := fun _ => rfl
  label := fun _ => 0
  label_target := fun _ => 0
  label_compat := fun _ => rfl
  lower_natural := fun _ => rfl
  upper_natural := fun _ => rfl

/-- The four K2 comparison alignments hold with `identityComparison` whenever
the frozen evaluation slice is the canonical identity evaluation system.  The
hypothesis is definitionally satisfied by the canonical evaluation bridge
(`SourceOutputWiring.sourceEvaluationBridgeOfVertical`), which fills
`R.evaluation.evaluation` with `identityEvaluationSystem`. -/
theorem identityComparison_alignments_of_evaluation_eq_identity
    (R : SourceTheorem311Realization l Label Choice)
    (h : R.evaluation.evaluation =
      SourceOutputWiring.identityEvaluationSystem Choice) :
    (identityComparison Choice).localMap = R.evaluation.evaluation.localMap ∧
    (identityComparison Choice).globalMap = R.evaluation.evaluation.globalMap ∧
    (identityComparison Choice).lower = R.evaluation.evaluation.localComp ∧
    (identityComparison Choice).upper = R.evaluation.evaluation.globalComp := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h] <;> rfl

/-- Item 28 consumption: the K2 Frobenioid boundary from an arbitrary link
layer with the four comparison alignments discharged by the identity
evaluation hypothesis. -/
def k2FrobenioidBoundaryOfIdentityEvaluation
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (L : PrimeStripFrobenioidLinkLayer X Y)
    (h : R.evaluation.evaluation =
      SourceOutputWiring.identityEvaluationSystem Choice) :
    K2FrobenioidBoundary R K X Y :=
  k2FrobenioidBoundaryOfLinkLayer R K L (identityComparison Choice)
    (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl)

/-- Nonempty form of `k2FrobenioidBoundaryOfIdentityEvaluation`. -/
theorem k2FrobenioidBoundary_nonempty_of_identityEvaluation
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (L : PrimeStripFrobenioidLinkLayer X Y)
    (h : R.evaluation.evaluation =
      SourceOutputWiring.identityEvaluationSystem Choice) :
    Nonempty (K2FrobenioidBoundary R K X Y) :=
  ⟨k2FrobenioidBoundaryOfIdentityEvaluation R K L h⟩

/-! ## 2. Global finite-model link layer (self-link) -/

/-- The global self-link of the finite model: the `PrimeStripFrobenioidLinkLayer`
on `FinitePlaceValueFamily s` whose local and global kernels are both the
total-degree kernel and whose `mod`/`MOD` maps are the identity.  It is built
through the value-map entry (`primeStripFrobenioidLinkLayerOfValueMaps`) from
the additive total-degree value map. -/
def finitePlaceSelfLinkLayer (s : Finset RationalPrimePlace) :
    PrimeStripFrobenioidLinkLayer (FinitePlaceValueFamily s)
      (FinitePlaceValueFamily s) :=
  primeStripFrobenioidLinkLayerOfValueMaps
    (fun f => (finitePlaceTotalDegreeFun s f).toAdd)
    (fun f g => finitePlaceTotalDegreeFun_mul_toAdd s f g)
    (by simp)
    id (fun _ => rfl)
    (fun f => (finitePlaceTotalDegreeFun s f).toAdd)
    (fun f g => finitePlaceTotalDegreeFun_mul_toAdd s f g)
    (by simp)
    id (fun _ => rfl)
    id (fun _ => rfl) (fun _ => rfl)
    id (fun _ => rfl) (fun _ => rfl)

/-- Global existence (finite model): the link-layer contract is inhabited on
the global carrier for every finite place set, unconditionally. -/
theorem finitePlaceSelfLinkLayer_nonempty (s : Finset RationalPrimePlace) :
    Nonempty (PrimeStripFrobenioidLinkLayer (FinitePlaceValueFamily s)
      (FinitePlaceValueFamily s)) :=
  ⟨finitePlaceSelfLinkLayer s⟩

/-- Global K2 boundary of the finite model over the global carrier, from the
self-link: the only remaining hypothesis is the identity-evaluation equation
(definitional for the canonical bridge). -/
theorem k2FrobenioidBoundary_nonempty_of_finitePlaceSelfLink
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    (s : Finset RationalPrimePlace)
    (h : R.evaluation.evaluation =
      SourceOutputWiring.identityEvaluationSystem Choice) :
    Nonempty (K2FrobenioidBoundary R K
      (FinitePlaceValueFamily s) (FinitePlaceValueFamily s)) :=
  k2FrobenioidBoundary_nonempty_of_identityEvaluation R K
    (finitePlaceSelfLinkLayer s) h

end

end K1K2Realization

end LeanFormal.IUT
