import tmp.sheaf.xif.paper.PaperSourceGeometryActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.Theta.GaussianKernel

/-!
# Completion-valued q / theta / Kummer action bridge

The value model of PaperSourceGeometryActual replaces the abstract value monoid
by the actual unit group of the local completion, with valueToCompletion the
genuine unit coercion.  This file puts actual q, q-theta and q-power Kummer
actions on that completion-valued carrier, and proves their exact
valueToCompletion compatibility.  It also records the actual source Kummer
arrow/layer from LogKummerCorrespondenceFromSource.

Exact gap: the actual source Kummer arrow acts on TimesMuQuotient of the
strip value monoid; no actual map from that abstract strip value monoid to the
completion value carrier is constructed.  The q-power action below is the
actual completion-unit action, not a fake identification with the strip arrow.

No sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperSourceGeometryKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open CompletionValuedSourceGeometry
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {p : Nat} [Fact p.Prime]
variable (G : CompletionValuedSourceGeometry
  (l := l) (K := I.initial.arithmetic.Fmod) (p := p) V)

/-- The actual q unit at a completion-valued source place. -/
noncomputable def completionValueQ (v : V) : valueCarrier G v :=
  G.qUnit v

theorem completionValueQ_eq_thetaPacket (v : V) :
    G.thetaPacket.q = ‖(completionValueQ I G v : CommonPrimeCompletion (G.place v))‖ :=
  G.thetaPacket_q_eq v

/-- The q unit maps to its actual completion value. -/
theorem valueToCompletion_completionValueQ (v : V) :
    valueToCompletion G v (completionValueQ I G v) =
      ((completionValueQ I G v : valueCarrier G v) :
        CommonPrimeCompletion (G.place v)) := rfl

/-- The actual q-generated theta value at a signed label. -/
noncomputable def completionValueTheta
    (j : SignedLabel l.value) (v : V) : valueCarrier G v :=
  completionValueQ I G v ^ (gaussExponent j.1).toNat

/-- The theta value is a power of the actual q completion unit. -/
theorem completionValueTheta_eq (j : SignedLabel l.value) (v : V) :
    completionValueTheta I G j v =
      completionValueQ I G v ^ (gaussExponent j.1).toNat := rfl

/-- The actual completion-unit Kummer action by q powers. -/
noncomputable def completionValueKummerAction
    (m : Nat) (v : V) (u : valueCarrier G v) : valueCarrier G v :=
  completionValueQ I G v ^ m * u

/-- valueToCompletion intertwines the q-power Kummer action. -/
theorem valueToCompletion_completionValueKummerAction
    (m : Nat) (v : V) (u : valueCarrier G v) :
    valueToCompletion G v (completionValueKummerAction I G m v u) =
      (valueToCompletion G v (completionValueQ I G v)) ^ m *
        valueToCompletion G v u := by
  change (((completionValueQ I G v ^ m * u : valueCarrier G v) :
    CommonPrimeCompletion (G.place v))) = _
  rw [Units.val_mul, Units.val_pow_eq_pow_val]
  rfl

/-- valueToCompletion sends the theta value to the q-power completion image. -/
theorem valueToCompletion_completionValueTheta
    (j : SignedLabel l.value) (v : V) :
    valueToCompletion G v (completionValueTheta I G j v) =
      (valueToCompletion G v (completionValueQ I G v)) ^
        (gaussExponent j.1).toNat := by
  change ((completionValueQ I G v ^ (gaussExponent j.1).toNat : valueCarrier G v) :
    CommonPrimeCompletion (G.place v)) = _
  rw [Units.val_pow_eq_pow_val]
  rfl

/-- Actual source Kummer arrow at the core strip. -/
noncomputable def completionValueKummerArrow :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualKummerArrow I 0

/-- Actual source Kummer layer at the core strip. -/
noncomputable def completionValueKummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualVerticalKummerLayer I 0

/-- Actual completion-valued q/theta/Kummer data. -/
structure CompletionValuedKummerData where
  q : (v : V) → valueCarrier G v
  theta : (j : SignedLabel l.value) → (v : V) → valueCarrier G v
  kummerAction : (m : Nat) → (v : V) → valueCarrier G v → valueCarrier G v
  q_eq : q = completionValueQ I G
  theta_eq : theta = completionValueTheta I G
  kummerAction_eq : kummerAction = completionValueKummerAction I G
  kummerArrow : SourceKummerArrow (ActualKummerGroup (I := I))
    (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  kummerArrow_eq : kummerArrow = completionValueKummerArrow I
  kummerLayer : SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
    (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  kummerLayer_eq : kummerLayer = completionValueKummerLayer I

/-- The actual completion-valued q/theta/Kummer data. -/
noncomputable def completionValuedKummerData :
    CompletionValuedKummerData I G where
  q := completionValueQ I G
  theta := completionValueTheta I G
  kummerAction := completionValueKummerAction I G
  q_eq := rfl
  theta_eq := rfl
  kummerAction_eq := rfl
  kummerArrow := completionValueKummerArrow I
  kummerArrow_eq := rfl
  kummerLayer := completionValueKummerLayer I
  kummerLayer_eq := rfl

/-- The q projection is the actual q unit. -/
theorem completionValuedKummerData_q :
    (completionValuedKummerData I G).q = completionValueQ I G := rfl

/-- The theta projection is the actual q-generated theta value. -/
theorem completionValuedKummerData_theta :
    (completionValuedKummerData I G).theta = completionValueTheta I G := rfl

/-- The action projection is the actual q-power action. -/
theorem completionValuedKummerData_kummerAction :
    (completionValuedKummerData I G).kummerAction =
      completionValueKummerAction I G := rfl

/-- The source Kummer arrow projection is actualKummerArrow. -/
theorem completionValuedKummerData_kummerArrow :
    (completionValuedKummerData I G).kummerArrow = actualKummerArrow I 0 := rfl

/-- The source Kummer layer projection is actualVerticalKummerLayer. -/
theorem completionValuedKummerData_kummerLayer :
    (completionValuedKummerData I G).kummerLayer =
      actualVerticalKummerLayer I 0 := rfl

end LeanFormal.IUT.XiFPaper.PaperSourceGeometryKummerActual
