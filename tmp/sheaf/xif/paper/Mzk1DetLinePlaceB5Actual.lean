/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.AbsTopIII07NormalizedLocalVolumeActual
import Mathlib.Tactic

/-! # Route B #3 step 3: per-place B5 interface (localizedLine + DVR generator + scaling law)

Minimal scheme agreed with the plan:
* a generator `x` of the rank-one localized lattice `localizedLine I v` over `O_v`
  (DVR principal generator: named input `LocalGeneratorData`);
* the normalized-Haar scaling law `mu(a • S) = ||a|| * mu(S)`
  (`AbsTopIII07NormalizedLocalVolumeActual` flags it as NEXT STEP);
* the per-place B5 statement `log mu(H_v) - log mu(O_v) = -(v(x_H) - v(x_O)) log p`
  as an explicit named Prop `PlaceB5Target` (not asserted).
The global B4/B5 identity is already proved in `Mzk1DetLineConstructionActual`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.AbsTopIII07NormalizedLocalVolumeActual

variable {k : Type} [Field k] [NumberField k]

/-- The normalized local Haar scaling law `mu(a • S) = ||a|| * mu(S)`
(named input; paper AbsTopIII Prop 5.7 scaling law, flagged as NEXT in AbsTopIII07). -/
def LocalHaarScalingLaw (K : Type*) [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] : Prop :=
  ∀ (a : K) (S : Set K), MeasurableSet S →
    normalizedHaar (K := K) ((fun x : K => a * x) '' S) = ‖a‖₊ * normalizedHaar (K := K) S

/-- A generator of the actual place-level localization of a line bundle, with the
span identity over the completed valuation ring. -/
structure LocalGeneratorData (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) where
  generator : LocalField (k := k) v
  span_eq : localizedLine (k := k) I v =
    Submodule.span (LocalRing (k := k) v) {generator}

/-- Existence of a principal generator for the localized line (DVR principal-ideal input). -/
def LocalPrincipalGenerator (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) : Prop :=
  Nonempty (LocalGeneratorData (k := k) I v)

/-- The per-place log-volume read from the generator (normalized by `mu(O_v)=1`). -/
def placeLogVolume {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v) : Real :=
  - Real.log ‖d.generator‖

/-- **Per-place B5 target**: the difference of the two place-level log-volumes equals
the negative valuation difference times `log p`; the integer valuations are supplied
as data (they are the p-adic valuations of the two generators). -/
def PlaceB5Target {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (dH : LocalGeneratorData (k := k) H v) (dO : LocalGeneratorData (k := k) O v)
    (vH vO : Int) (logp : Real) : Prop :=
  placeLogVolume dH - placeLogVolume dO = - (((vH - vO : Int) : Real)) * logp

def placeB5Rows : List (String × String × String) :=
  [ ("LocalGeneratorData", "generator of localizedLine over O_v + span identity", "DEF (minimal scheme)"),
    ("LocalPrincipalGenerator", "DVR principal generator existence", "GAP (named input; Mathlib PID submodule tooling)"),
    ("LocalHaarScalingLaw", "mu(a • S) = ||a|| mu(S)", "GAP (named input; AbsTopIII07 NEXT STEP)"),
    ("placeLogVolume", "-log||generator|| (mu(O_v)=1)", "DEF"),
    ("PlaceB5Target", "log mu(H_v)-log mu(O_v) = -(v xH - v xO) log p", "GAP (target Prop; not asserted)"),
    ("global B4/B5", "log D(H,O)=log H-log O", "PROVED (Mzk1DetLineConstructionActual)"),
    ("step 4 arch", "Mzk1NormArchCHArcActual / NormArchDegreeActual / archCK", "GREEN entries"),
    ("step 5 Ob33", "replace named identification using globalLogVolume_relativeDetLine + Ob33DetLine", "NEXT (await shehdd Ob33DetLine green)") ]

theorem placeB5Rows_length : placeB5Rows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual

end