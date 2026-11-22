import tmp.sheaf.xif.paper.S3138SourceProcessionProfileActual
import LeanFormal.IUT.IUTI.HodgeTheater.History
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3138: actual source procession carrier and Step XI input

Third piece of the source-level Step XI bridge.  From a genuine `OriginalInput`
this file builds the actual `ParametricTheorem311.Carrier` (core, profile and
the same-level connector) and the actual `SourceProcessionBoundary.Input` of
IUT III Theorem 3.11, replacing the finite Q(i)-at-5 model as the only
inhabitant.

The connector between two source choices is the pair of actual lattice
translations taking the first coordinate representative to the second (both
steps horizontal, both level-preserving); its target law is proved from the
actual `I.translate` algebra and the index equivalence.

The Step XI input uses the actual theater at `(n,m)`, its reflexive singleton
history (a genuine dependent history object, not an empty placeholder), the
actual source carrier, and the actual Theta log-volume at the base choice.
Its route normal form is the general parametric theorem
`routeTarget_level_eq_budget` applied to the actual carrier.

Source: IUT III, Theorem 3.11; IUT I, Hodge-theater histories.
Consumers: `S3138SourceStepXIActual` (wall / normalization / assembly).
-/

namespace LeanFormal.IUT.XiFPaper.S3138SourceProcessionCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.SourceProcessionBoundary
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionProfileActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The same-level connector along actual lattice translations -/

/-- The connector between two source choices: the two actual lattice
translations taking the coordinates of `a` to the coordinates of `b`.  Both
steps are horizontal. -/
noncomputable def sourceStepXIConnector
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (a b : SourceStepXIChoice I) : List (RouteStep SourceStepXILabel) :=
  [RouteStep.ind1 ((I.index_equiv b.1).1 - (I.index_equiv a.1).1),
   RouteStep.ind2 ((I.index_equiv b.1).2 - (I.index_equiv a.1).2)]

/-- Every step of the source connector is horizontal. -/
theorem sourceStepXIConnector_horizontal
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (a b : SourceStepXIChoice I) :
    ∀ step ∈ sourceStepXIConnector I a b, horizontal step := by
  intro step hstep
  simp [sourceStepXIConnector] at hstep
  rcases hstep with rfl | rfl
  · exact horizontal_of_ind1 _
  · exact horizontal_of_ind2 _

/-- The source connector reaches the target choice at equal level. -/
theorem sourceStepXIConnector_apply
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (a b : SourceStepXIChoice I)
    (hlevel : (sourceStepXICore I).level a = (sourceStepXICore I).level b) :
    applyRoute (sourceStepXICore I) (sourceStepXIConnector I a b) a = b := by
  change (I.translate 0 ((I.index_equiv b.1).2 - (I.index_equiv a.1).2)
      (I.translate ((I.index_equiv b.1).1 - (I.index_equiv a.1).1) 0 a.1),
      a.2) = b
  apply Prod.ext
  · rw [I.translate_add]
    simp only [add_zero, zero_add]
    calc
      I.translate ((I.index_equiv b.1).1 - (I.index_equiv a.1).1)
          ((I.index_equiv b.1).2 - (I.index_equiv a.1).2) a.1
          = I.translate ((I.index_equiv b.1).1 - (I.index_equiv a.1).1)
              ((I.index_equiv b.1).2 - (I.index_equiv a.1).2)
              (I.indexOf (I.index_equiv a.1).1 (I.index_equiv a.1).2) := by
            rw [sourceStepXI_indexOf_indexEquiv]
      _ = I.indexOf
            ((I.index_equiv a.1).1 + ((I.index_equiv b.1).1 - (I.index_equiv a.1).1))
            ((I.index_equiv a.1).2 + ((I.index_equiv b.1).2 - (I.index_equiv a.1).2)) :=
            I.translate_theater _ _ _ _
      _ = I.indexOf (I.index_equiv b.1).1 (I.index_equiv b.1).2 := by
            rw [show (I.index_equiv a.1).1 +
                  ((I.index_equiv b.1).1 - (I.index_equiv a.1).1) =
                  (I.index_equiv b.1).1 by ring,
                show (I.index_equiv a.1).2 +
                  ((I.index_equiv b.1).2 - (I.index_equiv a.1).2) =
                  (I.index_equiv b.1).2 by ring]
      _ = b.1 := sourceStepXI_indexOf_indexEquiv I b.1
  · exact hlevel

/-! ## 2. The actual source carrier -/

/-- The actual source procession carrier: the source core, the source
log-volume profile, and the actual lattice-translation connector. -/
noncomputable def sourceStepXICarrier
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Carrier SourceStepXILabel (SourceStepXIChoice I) where
  core := sourceStepXICore I
  profile := sourceStepXIProfile I
  connector := sourceStepXIConnector I
  connector_horizontal := fun a b => sourceStepXIConnector_horizontal I a b
  connector_target_same_level := by
    intro a b hlevel
    exact sourceStepXIConnector_apply I a b hlevel
  ind3_level_eq := by
    intro n c
    rfl

/-- The carrier's core is the source core (definitional projection). -/
theorem sourceStepXICarrier_core
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (sourceStepXICarrier I).core = sourceStepXICore I := rfl

/-- The carrier's profile is the source log-volume profile. -/
theorem sourceStepXICarrier_profile
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (sourceStepXICarrier I).profile = sourceStepXIProfile I := rfl

/-! ## 3. The actual source-level Step XI input -/

/-- The actual `SourceProcessionBoundary.Input` built from the original input:
the theater at `(n,m)`, its reflexive singleton dependent history, the actual
source carrier, and the actual theater Theta log-volume at the base choice. -/
noncomputable def sourceStepXIInput
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    SourceProcessionBoundary.Input.{ua, uv, upi, umon, 0, ui}
      (l := l) (V := V) (Label := SourceStepXILabel)
      (Choice := SourceStepXIChoice I) where
  theater := I.theaterAt n m
  history := HodgeTheaterHistory.singleton (I.theaterAt n m)
  carrier := sourceStepXICarrier I
  baseChoice := SourceStepXIBase I
  baseChoice_eq := rfl
  packetVolume := fun c => (sourceStepXICarrier I).profile.logVolume c
  packetVolume_eq_profile := by
    intro c
    rfl
  base_packetVolume_eq_theta := by
    show sourceStepXILogVolume I (SourceStepXIBase I) =
      (I.theaterAt n m).thetaPacket.logVolume
    exact sourceStepXIThetaLogVolume_eq I (I.indexOf 0 0) (I.indexOf n m)
  target_q := (I.theaterAt n m).thetaPacket.q
  target_q_eq := rfl
  history_q_eq := rfl
  route_normal_form := by
    intro route
    refine ⟨((routeTarget (sourceStepXICarrier I) route
        (SourceStepXIBase I)).1, 0), verticalBudget route, ?_, ?_⟩
    · rfl
    · apply Prod.ext
      · rfl
      · have h := routeTarget_level_eq_budget
            (sourceStepXICarrier I) route (SourceStepXIBase I)
        simpa [sourceStepXICarrier, sourceStepXICore, SourceStepXIBase] using h

/-- The Step XI input's theater is the actual theater at `(n,m)`. -/
theorem sourceStepXIInput_theater
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceStepXIInput I n m).theater = I.theaterAt n m := rfl

/-- The Step XI input's carrier is the actual source carrier. -/
theorem sourceStepXIInput_carrier
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceStepXIInput I n m).carrier = sourceStepXICarrier I := rfl

/-- The Step XI input's base is the actual source base choice. -/
theorem sourceStepXIInput_baseChoice
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceStepXIInput I n m).baseChoice = SourceStepXIBase I := rfl

/-- The base packet volume of the actual boundary is the actual theater Theta
log-volume of the chosen theater. -/
theorem sourceStepXIInput_base_theta
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceStepXIInput I n m).packetVolume (SourceStepXIBase I) =
      (I.theaterAt n m).thetaPacket.logVolume :=
  (sourceStepXIInput I n m).base_packetVolume_eq_theta

end LeanFormal.IUT.XiFPaper.S3138SourceProcessionCarrierActual

end
