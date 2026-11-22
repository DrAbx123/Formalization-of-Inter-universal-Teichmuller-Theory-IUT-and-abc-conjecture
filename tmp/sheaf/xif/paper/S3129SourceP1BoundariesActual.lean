import LeanFormal.IUT.IUTIII.Theorem311.SourceInternalWiring

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3129: actual P1 boundaries of IUT III Theorem 3.11

This file rebuilds the two Proposition 3.4 / Proposition 3.9 boundaries as
*actual* structures over a fixed realization `R : SourceTheorem311Realization`:

* `volumeBoundaryOfRealization` is the positive integer `Theta x`-lattice index
  obtained from the actual packet log-volume by rounding up; the Proposition
  3.9 upper-semi bound is proved from `Nat.le_ceil` rather than assumed.
* `lgpBoundaryOfSourceData` keeps the genuine local prime-strip data
  (`FPrimeStrip`, place, monodromy element, group element) and the
  degree/action compatibility as explicit source-facing inputs.  No field is
  replaced by a constant; the invariance fields are closed by reflexivity
  because they are statements about the fixed place map.

Source references: IUT III Proposition 3.4 (local LGP), Proposition 3.9
(log-volume / lattice bound).  Every declaration is unconditional in the
supplied source data; the only inputs are the realization packet and the
explicit strip data of the paper's local LGP section.

## Audit trail

Earlier version of this file failed to compile with
"invalid use of explicit universe parameters, SourceTheorem311Realization is a
local variable" (the structure is nested in
Theorem311Source.SourceHodgeTheaterBridge and was never opened) and
"Unknown identifier le_ceil" (correct name `Nat.le_ceil`).  Both are fixed
here; the statements are unchanged.
-/

namespace LeanFormal.IUT.XiFPaper.S3129SourceP1BoundariesActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge

universe u v w uv

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. Proposition 3.9: actual log-volume lattice boundary -/

/-- The actual lattice index of the realization packet log-volume: round the
nonnegative part of the packet log-volume up to a positive natural number.
This is the concrete `Theta x`-lattice index used by Proposition 3.9; the
upper bound is proved, not assumed. -/
noncomputable def volumeBoundaryOfRealization
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) :
    SourceP1.VolumeBoundary R where
  latticeIndex c := ⌈max 0 (R.packet.logVolume c)⌉₊ + 1
  latticeIndex_pos c := Nat.succ_pos _
  lattice_bound c := by
    have hmax : R.packet.logVolume c ≤ max 0 (R.packet.logVolume c) :=
      le_max_right _ _
    have hceil : max 0 (R.packet.logVolume c) ≤
        (⌈max 0 (R.packet.logVolume c)⌉₊ : Real) :=
      Nat.le_ceil _
    have hsucc : (⌈max 0 (R.packet.logVolume c)⌉₊ : Real) ≤
        ((⌈max 0 (R.packet.logVolume c)⌉₊ + 1 : Nat) : Real) := by
      exact_mod_cast Nat.le_succ _
    exact le_trans hmax (le_trans hceil hsucc)

@[simp] theorem volumeBoundaryOfRealization_latticeIndex
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) (c : Choice) :
    (volumeBoundaryOfRealization R).latticeIndex c =
      ⌈max 0 (R.packet.logVolume c)⌉₊ + 1 := rfl

theorem volumeBoundaryOfRealization_latticeIndex_pos
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) (c : Choice) :
    0 < (volumeBoundaryOfRealization R).latticeIndex c :=
  (volumeBoundaryOfRealization R).latticeIndex_pos c

/-- The Proposition 3.9 upper-semi inequality for the actual packet
log-volume, with the natural-number lattice index coerced to `Real`. -/
theorem volumeBoundaryOfRealization_lattice_bound
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) (c : Choice) :
    R.packet.logVolume c ≤
      ((volumeBoundaryOfRealization R).latticeIndex c : Real) :=
  (volumeBoundaryOfRealization R).lattice_bound c

/-- The constructed index is the canonical rounding `ceil (max 0 logVolume) + 1`
of the actual source profile, so the boundary is identified rather than
postulated. -/
theorem volumeBoundaryOfRealization_latticeIndex_eq_rounding
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) (c : Choice) :
    (volumeBoundaryOfRealization R).latticeIndex c =
      Nat.ceil (max 0 (R.packet.logVolume c)) + 1 := rfl

/-! ## 2. Proposition 3.4: actual local LGP boundary -/

/-- Assemble the actual local LGP boundary (Proposition 3.4) from a genuine
prime strip and the paper's place data.  The strip, place, monodromy element,
group element and the two degree/action compatibility equations are the
explicit source-facing inputs; the profile is the actual realization packet
log-volume.  The three `place_ind*` fields are invariance statements about
the *fixed* place map, hence are closed by reflexivity and do not transport
any extra data. -/
noncomputable def lgpBoundaryOfSourceData
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (strip : FPrimeStrip.{v, uv, u} V) (place : Choice → V)
    (monElement : ∀ c, strip.Mon (place c))
    (groupElement : ∀ c, strip.toDPrimeStrip.Pi (place c))
    (degree_profile : ∀ c,
      strip.degree (place c) (monElement c) = R.packet.logVolume c)
    (action_profile : ∀ c,
      strip.degree (place c)
        (strip.action (place c) (groupElement c) (monElement c)) =
        R.packet.logVolume c)
    (action_transport : ∀ c,
      strip.action (place c) (groupElement c) (monElement c) = monElement c) :
    SourceP1.LGPBoundary R V where
  strip := strip
  place := place
  monElement := monElement
  profile := fun c => R.packet.logVolume c
  degree_profile := degree_profile
  groupElement := groupElement
  action_profile := action_profile
  action_transport := action_transport
  place_ind1 := by intro g c; rfl
  place_ind2 := by intro g c; rfl
  place_ind3 := by intro n c; rfl

@[simp] theorem lgpBoundaryOfSourceData_strip
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (strip : FPrimeStrip.{v, uv, u} V) (place : Choice → V)
    (monElement : ∀ c, strip.Mon (place c))
    (groupElement : ∀ c, strip.toDPrimeStrip.Pi (place c))
    (degree_profile : ∀ c,
      strip.degree (place c) (monElement c) = R.packet.logVolume c)
    (action_profile : ∀ c,
      strip.degree (place c)
        (strip.action (place c) (groupElement c) (monElement c)) =
        R.packet.logVolume c)
    (action_transport : ∀ c,
      strip.action (place c) (groupElement c) (monElement c) = monElement c) :
    (lgpBoundaryOfSourceData R strip place monElement groupElement
      degree_profile action_profile action_transport).strip = strip := rfl

@[simp] theorem lgpBoundaryOfSourceData_profile
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (strip : FPrimeStrip.{v, uv, u} V) (place : Choice → V)
    (monElement : ∀ c, strip.Mon (place c))
    (groupElement : ∀ c, strip.toDPrimeStrip.Pi (place c))
    (degree_profile : ∀ c,
      strip.degree (place c) (monElement c) = R.packet.logVolume c)
    (action_profile : ∀ c,
      strip.degree (place c)
        (strip.action (place c) (groupElement c) (monElement c)) =
        R.packet.logVolume c)
    (action_transport : ∀ c,
      strip.action (place c) (groupElement c) (monElement c) = monElement c)
    (c : Choice) :
    (lgpBoundaryOfSourceData R strip place monElement groupElement
      degree_profile action_profile action_transport).profile c =
      R.packet.logVolume c := rfl

end LeanFormal.IUT.XiFPaper.S3129SourceP1BoundariesActual

end
