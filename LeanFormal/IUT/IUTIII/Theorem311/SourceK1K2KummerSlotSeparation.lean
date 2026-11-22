import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2CardReduction
import Mathlib.Tactic

/-!
  # kappa boundary card: interface-legal inhabitant vs arithmetic Kummer bijection
  (run k1k2-realization-20261016, three-artifact package)

  The kappa slot of `k1BoundaryOfLogShellPresentation` and of the item-27/28
  records has type `∀ c : Choice, LabelledKummerIso Choice Choice`.  The frozen
  `LabelledKummerIso` record (SourceFaithfulBoundary.lean:196) has exactly the
  fields `map`, `inverse`, `left_inverse`, `right_inverse`, `label`,
  `label_map`; it imposes no compatibility with `P.ind3` or `Q.logVolume`.

  This file records the boundary between an *interface-legal inhabitant* of the
  slot and an *arithmetic Kummer bijection*:

  * any labelling `A -> Nat` yields an admissible slot
    (`labelledKummerRelabel`), so the slot is inhabited for every `Choice`;
  * the slot does not determine the label: there are two admissible
    inhabitants with the same underlying map and different labels
    (`labelledKummerIso_map_does_not_determine_label`,
    `kummerSlotFamily_map_does_not_determine_label`), and the same freedom
    persists in the assembled boundary
    (`k1FromImageCards_labelledKummer_slot_free`);
  * the arithmetic upgrade route inside the tree is conditional on an
    injective Kummer lift: `labelledKummerIsoOfInjectiveLift` /
    `labelledKummerIso_nonempty_of_localKummerRootRealizationFor`
    (SourceK1K2Realization, E3), whose missing hypothesis is precisely the
    injectivity of the root polynomial lift.  The ordered-layer contract
    (`VerticalLogKummer` ordered layer) supplies only `Real`-valued monotone
    transport laws and contains no `LabelledKummerIso`-typed object; hence no
    Choice-level Kummer bijection is derivable from it.

  Status boundary: nothing here proves an arithmetic Kummer double bijection;
  the card records exactly why the frozen slot cannot supply one and which
  hypothesis (injective lift / Kummer nondegeneracy) the upgrade needs.
-/

set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe u v

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. Free relabelling of the slot -/

/-- Any labelling `A -> Nat` gives an admissible inhabitant of the kappa slot:
the identity bijection with the prescribed label function.  Only
`label_map` has to be checked, and `inverse (map a) = a` definitionally. -/
def labelledKummerRelabel (A : Type u) (lab : A → Nat) :
    LabelledKummerIso A A where
  map := id
  inverse := id
  left_inverse := fun _ => rfl
  right_inverse := fun _ => rfl
  label := lab
  label_map := fun _ => rfl

/-- The label of the relabelled slot is the prescribed one. -/
theorem labelledKummerRelabel_label (A : Type u) (lab : A → Nat) (a : A) :
    (labelledKummerRelabel A lab).label a = lab a :=
  rfl

/-- The identity labelled Kummer iso with constant label one: same underlying
bijection as `labelledKummerIdentity`, different label. -/
def labelledKummerIdentityLabelOne (A : Type u) : LabelledKummerIso A A :=
  labelledKummerRelabel A (fun _ => 1)

theorem labelledKummerIdentityLabelOne_label (A : Type u) (a : A) :
    (labelledKummerIdentityLabelOne A).label a = 1 :=
  rfl

/-- The slot admits any labelling: for every `A`, a point `a` and a label
function `lab`, there is an admissible inhabitant whose map is the identity
and whose label at `a` is `lab a`. -/
theorem kummerSlot_label_free (A : Type u) (a : A) (lab : A → Nat) :
    ∃ κ : LabelledKummerIso A A, κ.map = id ∧ κ.label a = lab a :=
  ⟨labelledKummerRelabel A lab, rfl, rfl⟩
/-! ## 2. The slot does not determine the label -/

/-- Two admissible inhabitants of the slot with the same map and different
labels: the slot cannot pin down arithmetic label data. -/
theorem labelledKummerIso_map_does_not_determine_label
    (A : Type u) (a : A) :
    ∃ κ κ' : LabelledKummerIso A A,
      κ.map = κ'.map ∧ κ.label a ≠ κ'.label a :=
  ⟨labelledKummerIdentity A, labelledKummerIdentityLabelOne A, rfl, by
    intro h
    exact Nat.zero_ne_one h⟩

/-- Family-level form matching the kappa hypothesis shape
`∀ c : Choice, LabelledKummerIso Choice Choice`: two admissible families with
pointwise equal maps and a label difference at any given point. -/
theorem kummerSlotFamily_map_does_not_determine_label
    (Choice : Type v) (c₀ : Choice) :
    ∃ κ κ' : ∀ _c : Choice, LabelledKummerIso Choice Choice,
      (∀ c, (κ c).map = (κ' c).map) ∧ κ c₀ ≠ κ' c₀ :=
  ⟨fun _ => labelledKummerIdentity Choice,
    fun _ => labelledKummerIdentityLabelOne Choice,
    fun _ => rfl, by
      intro h
      exact Nat.zero_ne_one
        (congrArg (fun K : LabelledKummerIso Choice Choice => K.label c₀) h)⟩

/-- The freedom persists in the assembled K1 boundary: the two slot families
above are admissible arguments of `k1FromImageCards` and produce boundaries
whose `labelledKummer` fields differ at the base point, although the
underlying maps agree pointwise.  Consequently no value of the kappa slot is
determined by the three image cards; the tree supplies the identity
relabelling only. -/
theorem k1FromImageCards_labelledKummer_slot_free
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hInc : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (hWD : K1K2BoundaryReduction.ind3ImageWellDefined P Q)
    (hLift : K1K2BoundaryReduction.archimedeanTargetLift P Q) :
    (K1K2BoundaryReduction.k1FromImageCards P Q hInc hWD hLift
        (fun _ => labelledKummerIdentity Choice)).labelledKummer ≠
      (K1K2BoundaryReduction.k1FromImageCards P Q hInc hWD hLift
        (fun _ => labelledKummerIdentityLabelOne Choice)).labelledKummer ∧
    (∀ c : Choice,
      ((K1K2BoundaryReduction.k1FromImageCards P Q hInc hWD hLift
          (fun _ => labelledKummerIdentity Choice)).labelledKummer c).map =
        ((K1K2BoundaryReduction.k1FromImageCards P Q hInc hWD hLift
          (fun _ => labelledKummerIdentityLabelOne Choice)).labelledKummer c).map) := by
  constructor
  · intro h
    have hbase := congrFun h P.base
    exact Nat.zero_ne_one
      (congrArg (fun K : LabelledKummerIso Choice Choice => K.label P.base) hbase)
  · intro c
    rfl

/-- The labelled Kummer iso slot of the k1 boundary carries no arithmetic
coupling: it is inhabited by the identity bijection with any constant label,
so `label` is interface-legal data of the record, not a consequence of the
image cards. -/
theorem k1FromImageCards_label_constant_free
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hInc : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (hWD : K1K2BoundaryReduction.ind3ImageWellDefined P Q)
    (hLift : K1K2BoundaryReduction.archimedeanTargetLift P Q)
    (n : Nat) :
    (K1K2BoundaryReduction.k1FromImageCards P Q hInc hWD hLift
        (fun _ => labelledKummerRelabel Choice (fun _ => n))).labelledKummer
        = fun _ => labelledKummerRelabel Choice (fun _ => n) :=
  rfl

end

end K1K2Realization

end LeanFormal.IUT
