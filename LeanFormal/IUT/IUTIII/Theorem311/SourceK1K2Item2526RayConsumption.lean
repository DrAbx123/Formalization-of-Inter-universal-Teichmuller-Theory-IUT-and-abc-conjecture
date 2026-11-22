import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Item2526Consumption
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteOutputLawBundleVerticalWiring
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2CardReduction
import Mathlib.Tactic

/-!
  # Phase A: item 25/26 consumption with the ray-presentation vertical
  (run k1k2-realization-20261016, three-artifact package)

  The item-25/26 consumption theorems of `SourceK1K2Item2526Consumption`
  carry the identification hypothesis

  `hV : R.vertical = sourceVerticalRealizationOfLogShellPresentation ... kappa`

  relating the vertical element of a realization `R` to the item-27
  constructor.  This file discharges `hV` definitionally for the vertical
  element supplied by the accepted output-wiring ray route (Mendel's
  `SourceOutputWiring.sourceVerticalRealizationOfRayPresentation` and its
  consumer packages `sourceTheorem311RealizationOfRayPresentation`,
  `sourceInputOfRayPresentation`).  Both constructions read `toSource` of the
  same `k1BoundaryOfLogShellPresentation` assembly with the same kappa slot
  `fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice`, so the
  identification is `rfl`.

  Every theorem below is a specialization of an item-25/26 equation along the
  ray route; no existing statement or hypothesis is changed, and the κ slot
  agreement is itself recorded (`labelledKummerIdentityFamily_eq_rayIdentitySlot`).

  Status boundary: this is an alignment result between two conditional
  constructions over the same hypotheses `(P, Q, L, h, hpres, hind3,
  hunbounded, hsep, hclass)`.  It does not supply `P` or `Q`; the procession
  and packet remain the residual source gaps recorded in
  `SourceK1K2VerticalRealization` and the item-27/28 notes.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanFormal.IUT

universe u v w uv upi umon ui ux uy

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain
open OriginalInput

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {V : Type uv}

/-! ## 1. Alignment of the two vertical routes -/

/-- The vertical element produced by the accepted output-wiring ray route is
definitionally the item-27 constructor `sourceVerticalRealizationOfLogShellPresentation`
with the identity labelled Kummer family: both read `toSource` of the same
`k1BoundaryOfLogShellPresentation` assembly, and Mendel's kappa slot is fixed
to the same identity labelled Kummer iso. -/
theorem sourceVerticalRealization_rayPresentation_eq_logShellPresentation
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c')) :
    SourceOutputWiring.sourceVerticalRealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass =
      sourceVerticalRealizationOfLogShellPresentation P Q L h hpres hind3
        hunbounded hsep hclass
        (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice) :=
  rfl

/-- The kappa slot of the ray route is the identity labelled Kummer family of
`SourceK1K2CardReduction` up to definitional unfolding. -/
theorem labelledKummerIdentityFamily_eq_rayIdentitySlot (Choice : Type v) :
    labelledKummerIdentityFamily (Choice := Choice) =
      (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice) :=
  rfl
/-! ## 2. Item 25 equations with `hV` discharged by `rfl` -/

theorem input_vertical_of_rayPresentation
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c')) :
    ((SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass).input).vertical =
      (k1BoundaryOfLogShellPresentation P Q L h hpres hind3 hunbounded hsep
        hclass
        (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice)).vertical :=
  input_vertical_of_realization_vertical_eq
    (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
      hpres hind3 hunbounded hsep hclass)
    L h hpres hind3 hunbounded hsep hclass
    (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice) rfl

theorem input_labelledKummer_of_rayPresentation
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (c : Choice) :
    ((SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass).input).labelledKummer c =
      K1K2BoundaryReduction.identityLabelledKummerIso Choice :=
  input_labelledKummer_of_realization_vertical_eq
    (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
      hpres hind3 hunbounded hsep hclass)
    L h hpres hind3 hunbounded hsep hclass
    (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice) rfl c

theorem input_verticalSite_nonarchimedeanImage_of_rayPresentation
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (m : Nat) (S : Set Real) :
    ((SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass).input).verticalSite.nonarchimedeanImage
        m S =
      (k1BoundaryOfLogShellPresentation P Q L h hpres hind3 hunbounded hsep
        hclass
        (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice)).nonarchimedeanImage
        m S :=
  input_verticalSite_nonarchimedeanImage_of_realization_vertical_eq
    (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
      hpres hind3 hunbounded hsep hclass)
    L h hpres hind3 hunbounded hsep hclass
    (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice) rfl m S

theorem input_verticalSite_archimedeanImage_of_rayPresentation
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (m : Nat) (S : Set Real) :
    ((SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass).input).verticalSite.archimedeanImage
        m S =
      (k1BoundaryOfLogShellPresentation P Q L h hpres hind3 hunbounded hsep
        hclass
        (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice)).archimedeanImage
        m S :=
  input_verticalSite_archimedeanImage_of_realization_vertical_eq
    (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
      hpres hind3 hunbounded hsep hclass)
    L h hpres hind3 hunbounded hsep hclass
    (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice) rfl m S
/-! ## 3. Item 26 equations with `hV` discharged by `rfl` -/

theorem k1OfRealization_vertical_of_rayPresentation
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c')) :
    (k1OfRealization
        (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
          hpres hind3 hunbounded hsep hclass)).vertical =
      (k1BoundaryOfLogShellPresentation P Q L h hpres hind3 hunbounded hsep
        hclass
        (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice)).vertical :=
  k1OfRealization_vertical_of_realization_vertical_eq
    (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
      hpres hind3 hunbounded hsep hclass)
    L h hpres hind3 hunbounded hsep hclass
    (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice) rfl

theorem k1OfRealization_labelledKummer_of_rayPresentation
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (c : Choice) :
    (k1OfRealization
        (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
          hpres hind3 hunbounded hsep hclass)).labelledKummer c =
      K1K2BoundaryReduction.identityLabelledKummerIso Choice :=
  k1OfRealization_labelledKummer_of_realization_vertical_eq
    (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
      hpres hind3 hunbounded hsep hclass)
    L h hpres hind3 hunbounded hsep hclass
    (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice) rfl c

/-- Item 26 over the ray route: the canonical internal wiring with the
link-layer K2 record, with the realization supplied by the ray-presentation
constructor (no `hV` hypothesis anywhere). -/
def sourceInternalWiringOfRayPresentation
    (I : OriginalInput.{u, uv, upi, umon, ui} l V)
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (Pp : H2SpokePermutation I)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (A : SourceH1H2Alignment I
      (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass))
    (Lk : PrimeStripFrobenioidLinkLayer X Y)
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap =
      (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass).evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap =
      (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass).evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower =
      (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass).evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper =
      (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass).evaluation.evaluation.globalComp) :
    SourceInternalWiring I
      (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
        hpres hind3 hunbounded hsep hclass) Pp X Y :=
  sourceInternalWiringOfLinkLayer I
    (SourceOutputWiring.sourceTheorem311RealizationOfRayPresentation P Q L h
      hpres hind3 hunbounded hsep hclass)
    Pp A Lk comparison comparison_local comparison_global comparison_lower
    comparison_upper

end

end K1K2Realization

end LeanFormal.IUT
