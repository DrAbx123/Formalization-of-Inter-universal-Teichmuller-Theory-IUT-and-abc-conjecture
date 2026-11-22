import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import tmp.sheaf.n8.closure.EtaRegionAdmVariation
import tmp.sheaf.n8.closure.EtaRegionAdmCorrect
import tmp.sheaf.n8.closure.P6L
import tmp.sheaf.n8.closure.P6AdmRedesign

/-!
# Eta q global region actual (carrier audit)

The actual qO region lives in

  QCompletion X = Completion (nativeFPlaceOverBad X)   (F-completion),

while a global region at badPlace X lives in

  localFieldAt X (badPlace X)   (base Fmod-completion).

These are different carriers; there is no production ring equivalence or
transport between them.  Therefore the requested global region
"qORegion at badPlace" cannot be constructed without an extra bridge.

This file records the exact bridge obligation and the conditional global
region/class construction.  It does not fabricate a bridge and does not use an
arbitrary region.  Exact no-go: the unconditional global qORegion class is not
constructed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQGlobalRegionActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.P6AdmRedesign
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaRegionAdmVariation
open LeanFormal.IUT.N8Closure.EtaRegionAdmCorrect
open LeanFormal.IUT.N8Closure.P6L

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]

/-- Actual qO carrier (F-completion). -/
abbrev QCarrier : Type _ := QCompletion X

/-- Base carrier at badPlace X (Fmod-completion). -/
abbrev BaseCarrier : Type _ := localFieldAt X (badPlace X)

/-- Exact missing carrier bridge from the F-completion qO carrier to the base
badPlace carrier, together with the qO image. -/
structure QORegionGlobalBridge where
  carrierEquiv : QCarrier X ≃ BaseCarrier X
  image : Set (BaseCarrier X)
  image_eq : image = carrierEquiv '' qORegion X

/-- Conditional global region: bridge image at badPlace, integralReference
elsewhere.  This is only conditional on the exact bridge. -/
noncomputable def qORegionGlobalRegion
    (B : QORegionGlobalBridge X) : GlobalRegion X := by
  classical
  exact fun v =>
    if h : v = badPlace X then h ▸ B.image else integralReference X v

/-- Conditional global class in the actual varying-region Rss. -/
noncomputable def qSourceClassGlobal
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    (B : QORegionGlobalBridge X) : VaryingRegionRss X mu :=
  Quotient.mk (sameBadMassSetoid X mu)
    (qORegionGlobalRegion X B)

/-- Exact no-go statement: the unconditional target is not constructed; only the
conditional class from the exact bridge is available. -/
def EtaQGlobalRegionUnconditionalTarget : Prop :=
  ∃ _B : QORegionGlobalBridge X, True

theorem etaQGlobalRegionUnconditionalTarget_iff :
    EtaQGlobalRegionUnconditionalTarget X ↔ Nonempty (QORegionGlobalBridge X) := by
  constructor
  · rintro ⟨B, _⟩; exact ⟨B⟩
  · rintro ⟨B⟩; exact ⟨B, trivial⟩

end LeanFormal.IUT.N8Closure.EtaQGlobalRegionActual
