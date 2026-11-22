import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Construction
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Realization
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripsFrobenioidLinks
import Mathlib.Tactic

set_option linter.unusedVariables false

/-!
  # K1/K2 realization to items 27/28 consumption wiring

  Consumes the installed `SourceK1K2Realization` (route: log-shell ray
  presentation) to wire the two frozen source-facing records of the
  necessary-chain map:

  * item 27 (`IUT-III.K1.vertical-log-kummer-boundary`,
    `SourceK1K2Construction.lean:666`): the conditional inhabitant
    `sourceVerticalRealizationOfLogShellPresentation` of the frozen
    `SourceVerticalRealization`, obtained as `toSource` of the card-assembled
    `K1VerticalBoundary`, with the two consumer laws read by item 25
    (`LeanFormal.IUT.Audit.sourceHodgeTheaterBridge`,
    `SourceHodgeTheaterBridge.lean:1966`) and item 26
    (`LeanFormal.IUT.Audit.theorem311InternalWiring`,
    `SourceInternalWiring.lean:1750`).

  * item 28 (`IUT-III.K2.frobenioid-mod-realification-boundary`,
    `SourceK1K2Construction.lean:679`): the consumer-shaped constructor
    `k2FrobenioidBoundaryOfLinkLayerOverRealization` producing the frozen
    `K2FrobenioidBoundary R (k1OfRealization R) X Y` already consumed at
    `SourceInternalWiring.lean:408` and `:1549`, together with the
    field-provenance ledger distinguishing constructed fields from the
    explicit source gates.

  No inverse law or source existence is inferred from the names of MOD/mod;
  every conditional hypothesis below is a named, unproved source gate.
-/

namespace LeanFormal.IUT

universe u v ux uy

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## Item 27: conditional inhabitant of `SourceVerticalRealization` -/

/-- Item 27 wiring.  Under the log-shell ray presentation with the three card
hypotheses (N1 `hind3`, A1 `hunbounded`, N2 `hsep`/`hclass`) and a labelled
Kummer slot `κ`, the frozen `SourceVerticalRealization` is inhabited by
`toSource` of the `K1VerticalBoundary` assembled in `SourceK1K2Realization`.
Each hypothesis is exactly the corresponding named source gate; no field is
manufactured from `OriginalInput`. -/
def sourceVerticalRealizationOfLogShellPresentation
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice) :
    SourceVerticalRealization P Q :=
  (k1BoundaryOfLogShellPresentation P Q L h hpres hind3 hunbounded hsep hclass κ).toSource

/-- Item 27 consumer law: the constructed realization transmits source-image
membership under `ind3` with an upper bound, exactly as the assembled K1
boundary does. -/
theorem sourceVerticalRealizationOfLogShellPresentation_nonarchimedean_upper
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice)
    (m : Nat) (c : Choice) (z : Real) (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage (P.ind3 m c) ∧ z ≤ y :=
  by
    have K := k1BoundaryOfLogShellPresentation P Q L h hpres hind3 hunbounded hsep hclass κ
    exact K.nonarchimedean_upper m c z hz

/-- Item 27 consumer law: the archimedean target-to-source lift, read on the
constructed realization. -/
theorem sourceVerticalRealizationOfLogShellPresentation_archimedean_target_lift
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice)
    (m : Nat) (c : Choice) (z : Real) (hz : z ∈ Q.possibleImage (P.ind3 m c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y :=
  by
    have K := k1BoundaryOfLogShellPresentation P Q L h hpres hind3 hunbounded hsep hclass κ
    exact K.archimedean_target_lift m c z hz

/-! ## Item 28: consumer-shaped K2 boundary and field ledger -/

/-- Item 28 wiring.  The frozen `K2FrobenioidBoundary R (k1OfRealization R) X Y`
consumed by `SourceInternalWiring` (`:408`, `:1549`) is produced from the
IUT-II link layer plus the supplied comparison package with its four alignment
equations; the K1 slot is the canonical projection `k1OfRealization R`. -/
def k2FrobenioidBoundaryOfLinkLayerOverRealization
    (R : SourceTheorem311Realization l Label Choice)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (L : PrimeStripFrobenioidLinkLayer X Y)
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap = R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap = R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower = R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper = R.evaluation.evaluation.globalComp) :
    K2FrobenioidBoundary R (k1OfRealization R) X Y :=
  k2FrobenioidBoundaryOfLinkLayer R (k1OfRealization R) L comparison
    comparison_local comparison_global comparison_lower comparison_upper

/-- Item 28 field ledger: provenance of the data fields of the constructed
boundary.  `localFrobenioid`/`globalFrobenioid` are the proven identity bridge
from the link-layer value kernels; `modMap`/`MODMap` and `comparison` are the
supplied directions verbatim; `upperSemi` is the K1 vertical direction.  The
law fields (`mod_degree` through `comparison_upper`) are supplied in the same
way from `L` and the four alignment hypotheses; no inverse law is added. -/
theorem k2FrobenioidBoundaryOfLinkLayerOverRealization_fieldLedger
    (R : SourceTheorem311Realization l Label Choice)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (L : PrimeStripFrobenioidLinkLayer X Y)
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap = R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap = R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower = R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper = R.evaluation.evaluation.globalComp) :
    (k2FrobenioidBoundaryOfLinkLayerOverRealization R L comparison
        comparison_local comparison_global comparison_lower comparison_upper).localFrobenioid =
        sourceProposition37FrobenioidOfValueKernel L.localFrobenioid ∧
      (k2FrobenioidBoundaryOfLinkLayerOverRealization R L comparison
        comparison_local comparison_global comparison_lower comparison_upper).globalFrobenioid =
        sourceProposition37FrobenioidOfValueKernel L.globalFrobenioid ∧
      (k2FrobenioidBoundaryOfLinkLayerOverRealization R L comparison
        comparison_local comparison_global comparison_lower comparison_upper).modMap = L.modMap ∧
      (k2FrobenioidBoundaryOfLinkLayerOverRealization R L comparison
        comparison_local comparison_global comparison_lower comparison_upper).MODMap = L.MODMap ∧
      (k2FrobenioidBoundaryOfLinkLayerOverRealization R L comparison
        comparison_local comparison_global comparison_lower comparison_upper).comparison =
        comparison ∧
      (k2FrobenioidBoundaryOfLinkLayerOverRealization R L comparison
        comparison_local comparison_global comparison_lower comparison_upper).upperSemi =
        (k1OfRealization R).vertical :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end K1K2Realization

end LeanFormal.IUT
