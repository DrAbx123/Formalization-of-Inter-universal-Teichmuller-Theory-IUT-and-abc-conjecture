import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2VerticalRealization
import LeanFormal.IUT.IUTIII.Theorem311.SourceInternalWiring
import Mathlib.Tactic

/-!
  # Items 25/26 consumption wiring (run k1k2-realization-20261016)

  Connects the constructed 27/28 artifacts to the two audit consumption
  sites:

  * item 25 `sourceHodgeTheaterBridge` (`SourceHodgeTheaterBridge.lean:1966`):
    the `Theorem311Source.Input` slots (`vertical`, `verticalSite.*`,
    `labelledKummer`) read through `SourceTheorem311Realization.input`;
  * item 26 `theorem311InternalWiring` (`SourceInternalWiring.lean:1750`):
    the canonical wiring `SourceInternalWiring.canonical` consumed at
    `SourceInternalWiring.lean:408` and `:1549`, rebuilt with the K2 record
    `k2FrobenioidBoundaryOfLinkLayerOverRealization`.

  Every statement is conditional on an identification
  `R.vertical = sourceVerticalRealizationOfLogShellPresentation ...`;
  no hypothesis of any existing statement is changed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe uv upi umon ui u v w ux uy

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain
open OriginalInput

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {V : Type uv}

/-! ## Item 25: `Input` slots of the bridge -/

theorem input_vertical_of_realization_vertical_eq
    (R : SourceTheorem311Realization l Label Choice)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation R.packet L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (R.procession.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (R.procession.ind3 m c) = h (R.procession.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice)
    (hV : R.vertical =
      sourceVerticalRealizationOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ) :
    (R.input).vertical =
      (k1BoundaryOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ).vertical := by
  rw [SourceTheorem311Realization.input_vertical_source, hV]
  rfl

theorem input_labelledKummer_of_realization_vertical_eq
    (R : SourceTheorem311Realization l Label Choice)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation R.packet L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (R.procession.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (R.procession.ind3 m c) = h (R.procession.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice)
    (hV : R.vertical =
      sourceVerticalRealizationOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ)
    (c : Choice) :
    (R.input).labelledKummer c = κ c := by
  have h1 : (R.input).labelledKummer = R.vertical.kummer := rfl
  rw [h1, hV]
  rfl

theorem input_verticalSite_nonarchimedeanImage_of_realization_vertical_eq
    (R : SourceTheorem311Realization l Label Choice)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation R.packet L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (R.procession.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (R.procession.ind3 m c) = h (R.procession.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice)
    (hV : R.vertical =
      sourceVerticalRealizationOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ)
    (m : Nat) (S : Set Real) :
    (R.input).verticalSite.nonarchimedeanImage m S =
      (k1BoundaryOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ).nonarchimedeanImage m S := by
  have h1 : (R.input).verticalSite.nonarchimedeanImage =
      R.vertical.nonarchimedeanImage := rfl
  rw [h1, hV]
  rfl

theorem input_verticalSite_archimedeanImage_of_realization_vertical_eq
    (R : SourceTheorem311Realization l Label Choice)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation R.packet L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (R.procession.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (R.procession.ind3 m c) = h (R.procession.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice)
    (hV : R.vertical =
      sourceVerticalRealizationOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ)
    (m : Nat) (S : Set Real) :
    (R.input).verticalSite.archimedeanImage m S =
      (k1BoundaryOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ).archimedeanImage m S := by
  have h1 : (R.input).verticalSite.archimedeanImage =
      R.vertical.archimedeanImage := rfl
  rw [h1, hV]
  rfl

/-! ## Item 26: canonical wiring with the link-layer K2 record -/

theorem k1OfRealization_vertical_of_realization_vertical_eq
    (R : SourceTheorem311Realization l Label Choice)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation R.packet L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (R.procession.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (R.procession.ind3 m c) = h (R.procession.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice)
    (hV : R.vertical =
      sourceVerticalRealizationOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ) :
    (k1OfRealization R).vertical =
      (k1BoundaryOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ).vertical := by
  rw [k1OfRealization_vertical, hV]
  rfl

theorem k1OfRealization_labelledKummer_of_realization_vertical_eq
    (R : SourceTheorem311Realization l Label Choice)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation R.packet L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (R.procession.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (R.procession.ind3 m c) = h (R.procession.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice)
    (hV : R.vertical =
      sourceVerticalRealizationOfLogShellPresentation R.procession R.packet
        L h hpres hind3 hunbounded hsep hclass κ)
    (c : Choice) :
    (k1OfRealization R).labelledKummer c = κ c := by
  rw [k1OfRealization_labelledKummer, hV]
  rfl

def sourceInternalWiringOfLinkLayer
    (I : OriginalInput.{u, uv, upi, umon, ui} l V)
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (P : H2SpokePermutation I)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (A : SourceH1H2Alignment I R)
    (L : PrimeStripFrobenioidLinkLayer X Y)
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap = R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap = R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower = R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper = R.evaluation.evaluation.globalComp) :
    SourceInternalWiring I R P X Y :=
  SourceInternalWiring.canonical A P
    (k2FrobenioidBoundaryOfLinkLayerOverRealization R L comparison
      comparison_local comparison_global comparison_lower comparison_upper)

theorem sourceInternalWiringOfLinkLayer_k1
    (I : OriginalInput.{u, uv, upi, umon, ui} l V)
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (P : H2SpokePermutation I)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (A : SourceH1H2Alignment I R)
    (L : PrimeStripFrobenioidLinkLayer X Y)
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap = R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap = R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower = R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper = R.evaluation.evaluation.globalComp) :
    (sourceInternalWiringOfLinkLayer I R P A L comparison comparison_local
      comparison_global comparison_lower comparison_upper).k1 =
      k1OfRealization R := rfl

theorem sourceInternalWiringOfLinkLayer_k2_upperSemi
    (I : OriginalInput.{u, uv, upi, umon, ui} l V)
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (P : H2SpokePermutation I)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (A : SourceH1H2Alignment I R)
    (L : PrimeStripFrobenioidLinkLayer X Y)
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap = R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap = R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower = R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper = R.evaluation.evaluation.globalComp) :
    (sourceInternalWiringOfLinkLayer I R P A L comparison comparison_local
      comparison_global comparison_lower comparison_upper).k2.upperSemi =
      (k1OfRealization R).vertical := rfl

end

end K1K2Realization

end LeanFormal.IUT
