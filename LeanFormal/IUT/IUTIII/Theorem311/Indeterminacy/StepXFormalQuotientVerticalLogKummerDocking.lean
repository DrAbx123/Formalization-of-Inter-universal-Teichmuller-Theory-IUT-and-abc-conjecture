/-
  Docking of the Step-(x) kernel supply to the source-facing vertical
  log-Kummer contract.

  `VerticalLogKummerCorrespondence` (IUT II, Sections 5-6; the ordered
  source/target layer contract consumed by the Frobenius-stripping /
  value-group layer, relay REQ-3) asks for a layered Kummer map whose
  images are monotone along the layer transport (`upperSemi`).  This
  module exhibits the constructed Q(i)-at-5 core as a concrete model:
  the layer family is the constant family of constructed processions,
  the transport step is the stage-one (Ind3) lift, the Kummer image is
  the lifted normalized log-volume into `Real`, and the upper-semi
  field is the level-translation law of the (Ind3) lift.  The layer
  preorders are vacuous (the contract does not use them); the
  meaningful content is the `upperSemi` law, proved here from
  `ProcessionChoice.ind3_upperSemiLevel`.

  Relative to the conditional supply of
  `StepXFormalQuotientConsumption.lean`, this file pins the transport
  to the canonical compatible Frobenius action
  (`ind3Lift_frobeniusCompatibility l 1`): the stage-one (Ind3) lift.
  A source-level Frobenius carrier for the Frobenioid/log-shell layers
  is not built here and remains the pending card recorded in
  `logs/coordination/finrank-ef-20261016.md`, Entry 17.
-/

import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.StepXFormalQuotientConsumption
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer

namespace LeanFormal.IUT

open MultiradialKernel
open MultiradialKernel.Core
open ConcreteFiniteTheorem311

noncomputable section

namespace StepXFormalQuotient

/-- The constructed Q(i)-at-5 core as a concrete inhabitant of the
vertical log-Kummer correspondence: `D = Real`, the layer family is the
constant family of constructed processions, the transport step is the
stage-one (Ind3) lift, and the Kummer image is the lifted normalized
log-volume.  The upper-semi field is the level-translation law; the
layer preorders are vacuous and unused by that law. -/
def verticalLogKummerOfConstructedCore (l : PrimeGeFive) :
    VerticalLogKummerCorrespondence :=
  letI : Preorder (ProcessionChoice l) :=
    { le := fun _ _ => True
      lt := fun _ _ => False
      le_refl := fun _ => trivial
      le_trans := fun _ _ _ _ _ => trivial
      lt_iff_le_not_ge := fun _ _ => ⟨False.elim, fun h => h.2 trivial⟩ }
  { D := Real
    ordD := inferInstance
    F := fun _ => ProcessionChoice l
    ordF := fun _ => inferInstance
    log := fun _ x => ProcessionChoice.ind3Lift 1 x
    kummer := fun m x => normalizedLogVolume l (ProcessionChoice.ind3Lift m x)
    upperSemi := fun m x => by
      simp only [normalizedLogVolume, ProcessionChoice.ind3_upperSemiLevel,
        Nat.cast_add]
      linarith }

/-- The docking's transport is the stage-one (Ind3) lift, i.e. the
canonical compatible Frobenius action of the Step-(x) module. -/
theorem verticalLogKummerOfConstructedCore_log_apply (l : PrimeGeFive)
    (m : Nat) (x : ProcessionChoice l) :
    (verticalLogKummerOfConstructedCore l).log m x =
      ProcessionChoice.ind3Lift 1 x := rfl

end StepXFormalQuotient

/-! ## 2. Frobenius compatibility of the ordered layers (relay REQ-3) -/

namespace VerticalLogKummerCorrespondence

/-- A Frobenius-compatible endomorphism of the ordered layers of a vertical
log-Kummer correspondence: an endomorphism of the layer family that commutes
with the log-link steps (the 1-compatibility of a naive Frobenius functor
with the Frobenius functor on the divisor monoid of [FrdI], Proposition 2.1,
(ii)) and does not lower the Kummer image in the order of the target (the
value/log-shell side of the Frobenius action; no degree is fixed, so any
iterate or conjugate qualifies). -/
structure LayerFrobeniusCompatibility (K : VerticalLogKummerCorrespondence)
    (frobenius : ∀ m : Nat, K.F m → K.F m) : Prop where
  log_comm : ∀ (m : Nat) (x : K.F m),
    frobenius (m + 1) (K.log m x) = K.log m (frobenius m x)
  kummer_mono : ∀ (m : Nat) (x : K.F m),
    K.kummer m x ≤ K.kummer m (frobenius m x)

namespace LayerFrobeniusCompatibility

/-- The identity action is compatible (the degree-one case). -/
theorem id (K : VerticalLogKummerCorrespondence) :
    LayerFrobeniusCompatibility K (fun _ x => x) :=
  ⟨fun _ _ => rfl, fun _ _ => le_refl _⟩

/-- Composition of compatible actions is compatible: the composite again
commutes with the log-link steps and does not lower the Kummer image. -/
theorem comp (K : VerticalLogKummerCorrespondence)
    {frob₁ frob₂ : ∀ m : Nat, K.F m → K.F m}
    (D₁ : LayerFrobeniusCompatibility K frob₁)
    (D₂ : LayerFrobeniusCompatibility K frob₂) :
    LayerFrobeniusCompatibility K (fun m x => frob₁ m (frob₂ m x)) := by
  obtain ⟨h₁log, h₁mono⟩ := D₁
  obtain ⟨h₂log, h₂mono⟩ := D₂
  exact ⟨fun m x => by rw [h₂log m x, h₁log m (frob₂ m x)],
    fun m x => (h₂mono m x).trans (h₁mono m (frob₂ m x))⟩

/-- A compatible action commutes with all iterated transports. -/
theorem transport_comm (K : VerticalLogKummerCorrespondence)
    {frobenius : ∀ m : Nat, K.F m → K.F m}
    (hD : LayerFrobeniusCompatibility K frobenius) :
    ∀ (m n : Nat) (x : K.F m),
      frobenius (m + n) (K.transport m n x) =
        K.transport m n (frobenius m x) := by
  obtain ⟨hlog, _⟩ := hD
  intro m n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      have hunfold : K.transport m (n + 1) x =
          K.log (m + n) (K.transport m n x) := rfl
      have hunfold2 : K.transport m (n + 1) (frobenius m x) =
          K.log (m + n) (K.transport m n (frobenius m x)) := rfl
      rw [hunfold, hunfold2]
      exact (hlog (m + n) (K.transport m n x)).trans
        (congrArg (K.log (m + n)) (ih x))

/-- Frobenius-conjugate dominance: every vertical iterate of the Frobenius
conjugate of a point dominates the original Kummer image -- the conditional
form of the value-side semi-compatibility of (Ind3) under a Frobenius
action. -/
theorem kummer_le_transport_conjugate (K : VerticalLogKummerCorrespondence)
    {frobenius : ∀ m : Nat, K.F m → K.F m}
    (hD : LayerFrobeniusCompatibility K frobenius)
    (m n : Nat) (x : K.F m) :
    K.kummer m x ≤
      K.kummer (m + n) (frobenius (m + n) (K.transport m n x)) := by
  obtain ⟨_, hmono⟩ := hD
  exact (K.kummer_le_transport m x n).trans (hmono (m + n) (K.transport m n x))

/-- Transported form of conjugate dominance: the conjugate may be taken
after the transport, by commutation. -/
theorem transport_conjugate_dominated (K : VerticalLogKummerCorrespondence)
    {frobenius : ∀ m : Nat, K.F m → K.F m}
    (hD : LayerFrobeniusCompatibility K frobenius)
    (m n : Nat) (x : K.F m) :
    K.kummer m x ≤ K.kummer (m + n) (K.transport m n (frobenius m x)) := by
  rw [← transport_comm K hD m n x]
  exact kummer_le_transport_conjugate K hD m n x

end LayerFrobeniusCompatibility

end VerticalLogKummerCorrespondence

namespace StepXFormalQuotient

/-- The degree-k (Ind3) lift is a compatible Frobenius action on the
constructed docking: it commutes with the step-one log link and does not
lower the lifted log-volume.  The case k = 1 recovers the canonical
compatible Frobenius action of the Step-(x) module; the family k ≥ 1
supplies the vertical Frobenius conjugates of the p-adic-Teichmuller
analogy (IUT III, Remark 3.12.3, (v); corpus :11589-11619). -/
theorem verticalLogKummerOfConstructedCore_frobeniusCompatibility
    (l : PrimeGeFive) (k : Nat) :
    VerticalLogKummerCorrespondence.LayerFrobeniusCompatibility
      (verticalLogKummerOfConstructedCore l)
      (fun _ => ProcessionChoice.ind3Lift k) :=
  ⟨fun m x => by
      change ProcessionChoice.ind3Lift k (ProcessionChoice.ind3Lift 1 x) =
        ProcessionChoice.ind3Lift 1 (ProcessionChoice.ind3Lift k x)
      rw [← ProcessionChoice.ind3_add 1 k x,
        ← ProcessionChoice.ind3_add k 1 x, Nat.add_comm 1 k],
    fun m x => by
      change normalizedLogVolume l (ProcessionChoice.ind3Lift m x) ≤
        normalizedLogVolume l
          (ProcessionChoice.ind3Lift m (ProcessionChoice.ind3Lift k x))
      simp only [normalizedLogVolume, ProcessionChoice.ind3_upperSemiLevel]
      have hcast : ((x.upperSemiLevel + m : Nat) : Real) ≤
          (((x.upperSemiLevel + k) + m : Nat) : Real) := by
        have hnat : x.upperSemiLevel + m ≤ (x.upperSemiLevel + k) + m := by
          omega
        exact_mod_cast hnat
      linarith⟩

end StepXFormalQuotient

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Status record for the vertical log-Kummer docking of the constructed
core. -/
def stepXFormalQuotientVerticalLogKummerDocking : Obligation :=
  { id := "IUT-III.StepX.vertical-log-kummer-docking"
    source :=
      "IUT II, Sections 5--6 (vertical log-Kummer correspondence); " ++
        "relay REQ-3 of the Frobenius-stripping / value-group layer"
    status := VerificationStatus.provedKernel
    note :=
      "The constructed core inhabits the source-facing " ++
        "`VerticalLogKummerCorrespondence` contract with `Real`-valued " ++
        "lifted normalized log-volumes, constant layer family and the " ++
        "stage-one (Ind3) lift as transport; its `upperSemi` field is " ++
        "proved from the level-translation law.  The source " ++
        "Frobenioid/log-shell carriers and a source Frobenius action " ++
        "remain open (Entry 17 of " ++
        "`logs/coordination/finrank-ef-20261016.md`)."
    dependsOn :=
      [ "IUT-III.StepX.formal-quotient-consumption",
        "IUT-II.vertical-log-kummer-correspondence" ] }

/-- Status record for the conditional Frobenius-compatibility layer of the
vertical log-Kummer correspondence (relay REQ-3). -/
def stepXFormalQuotientLayerFrobenius : Obligation :=
  { id := "IUT-III.StepX.layer-frobenius-compatibility"
    source :=
      "IUT III, Remark 3.12.3, (v) (Frobenius conjugates; (Ind3)); " ++
        "[FrdI], Proposition 2.1, (ii); relay REQ-3"
    status := VerificationStatus.provedKernel
    note :=
      "Conditional form of the value-side Frobenius action on an ordered " ++
        "vertical log-Kummer correspondence: a layer endomorphism that " ++
        "commutes with the log-link steps and does not lower the Kummer " ++
        "image has conjugate dominance across all iterated transports, is " ++
        "closed under composition, and admits the identity; the degree-k " ++
        "(Ind3) lifts of the constructed docking form a nonempty family " ++
        "of such actions.  The source Frobenioid carrier (sharp " ++
        "divisorial monoid) remains the pending card of Entries 17-18 of " ++
        "logs/coordination/finrank-ef-20261016.md."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer-correspondence",
        "IUT-III.StepX.vertical-log-kummer-docking" ] }

end LeanFormal.IUT.Audit
