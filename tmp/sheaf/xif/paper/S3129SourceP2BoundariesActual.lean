import LeanFormal.IUT.IUTIII.Theorem311.SourceInternalWiring

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3129: actual P2 boundaries of IUT III Theorem 3.11

This file rebuilds the Proposition 2.1 (labelled Kummer correspondence) and
Corollary 2.3 (permutation/spoke) boundaries over a fixed realization
`R : SourceTheorem311Realization`.

Actual data used:

* the labelled Kummer correspondence is the realization input arrow
  `R.input.labelledKummer c`; the degree/labelling maps are its actual
  `label` and `label (inverse -)` maps, so the degree transport law is the
  kernel-checked `label_map` field of the source arrow (no new data);
* the q-parameter is the actual packet determinant `R.packet.determinant c`,
  which carries its own positivity proof `R.packet.determinant_positive c`;
* the generic-family permutation is the actual
  `R.genericFamily.permutation` of Corollary 2.3.

Still source-facing explicit inputs (not constructible from the current
realization fields, and therefore NOT replaced by constants):

* the evaluation pair and its two transport equations of Proposition 2.1;
* the q-log transport law of Proposition 2.1;
* the spoke map and its permutation-invariance equation of Corollary 2.3.

The previous version of this file used undefined universe parameters and
contained a `sorry`; both are gone.  Every declaration below is a genuine
construction or a projection of the supplied realization.
-/

namespace LeanFormal.IUT.XiFPaper.S3129SourceP2BoundariesActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge

universe u v w

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. Corollary 2.3: permutation boundary -/

/-- Actual Corollary 2.3 boundary: the theater family and its permutation are
the realization's generic family; only the spoke map and its invariance are
source-facing inputs. -/
def S3129PermutationBoundaryOf
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (spoke : Choice → Choice)
    (hspoke : ∀ c, spoke (R.genericFamily.permutation c) = spoke c) :
    SourceP2.PermutationBoundary R where
  spoke := spoke
  spoke_permutation := hspoke

/-- The actual generic-family permutation of the realization. -/
def S3129GenericPermutationActual
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) :
    Equiv.Perm Choice :=
  R.genericFamily.permutation

/-- Consuming Corollary 2.3: its permutation slot is the actual generic-family
permutation, so the boundary does not re-choose a permutation. -/
theorem S3129_corollary23_permutation
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (spoke : Choice → Choice)
    (hspoke : ∀ c, spoke (R.genericFamily.permutation c) = spoke c) :
    (SourceP2.corollary23 (S3129PermutationBoundaryOf R spoke hspoke)).permutation =
      R.genericFamily.permutation := rfl

/-- The spoke slot of the constructed boundary is the supplied spoke, i.e.
Corollary 2.3 consumes it verbatim. -/
theorem S3129_corollary23_spoke
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (spoke : Choice → Choice)
    (hspoke : ∀ c, spoke (R.genericFamily.permutation c) = spoke c)
    (c : Choice) :
    (SourceP2.corollary23 (S3129PermutationBoundaryOf R spoke hspoke)).spoke c =
      spoke c := rfl

/-! ## 2. Proposition 2.1: labelled Kummer boundary -/

/-- The actual labelled Kummer arrow of the realization input at a choice. -/
def S3129LabelledKummerActual
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) (c : Choice) :
    LabelledKummerIso Choice Choice :=
  R.input.labelledKummer c

/-- Actual Proposition 2.1 boundary.  The correspondence is the actual
labelled Kummer isomorphism of the realization input; the degree function and
its inverse are its own labelling functions; the q-parameter is the positive
packet determinant.  The evaluation pair and the q-log transport law remain
explicit source data, exactly as in the paper's Proposition 2.1. -/
def S3129KummerBoundaryOfActual
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) (c : Choice)
    (evaluation evaluation_target : Choice → Real)
    (evaluation_map : ∀ a,
      evaluation_target ((R.input.labelledKummer c).map a) = evaluation a)
    (evaluation_inverse : ∀ b,
      evaluation ((R.input.labelledKummer c).inverse b) = evaluation_target b)
    (q_log : Choice → Real)
    (q_log_map : ∀ a,
      q_log ((R.input.labelledKummer c).inverse
        ((R.input.labelledKummer c).map a)) = q_log a) :
    SourceP2.KummerBoundary R where
  correspondence := R.input.labelledKummer c
  degree := fun a => (R.input.labelledKummer c).label a
  degree_inverse := fun b => (R.input.labelledKummer c).label
    ((R.input.labelledKummer c).inverse b)
  degree_map := fun a => (R.input.labelledKummer c).label_map a
  degree_inverse_map := fun b => rfl
  evaluation := evaluation
  evaluation_target := evaluation_target
  evaluation_map := evaluation_map
  evaluation_inverse := evaluation_inverse
  q_parameter := R.packet.determinant c
  q_positive := R.packet.determinant_positive c
  q_log := q_log
  q_log_map := q_log_map

/-- The correspondence consumed by Proposition 2.1 is the actual labelled
Kummer arrow, not a re-chosen one. -/
theorem S3129_proposition21_correspondence
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) (c : Choice)
    (evaluation evaluation_target : Choice → Real)
    (evaluation_map : ∀ a,
      evaluation_target ((R.input.labelledKummer c).map a) = evaluation a)
    (evaluation_inverse : ∀ b,
      evaluation ((R.input.labelledKummer c).inverse b) = evaluation_target b)
    (q_log : Choice → Real)
    (q_log_map : ∀ a,
      q_log ((R.input.labelledKummer c).inverse
        ((R.input.labelledKummer c).map a)) = q_log a) :
    (SourceP2.proposition21 (S3129KummerBoundaryOfActual R c evaluation
        evaluation_target evaluation_map evaluation_inverse q_log q_log_map)).correspondence =
      R.input.labelledKummer c := rfl

/-- The q-parameter of the claimed boundary is the actual packet determinant,
with positivity inherited from the realization packet. -/
theorem S3129_proposition21_q_parameter
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) (c : Choice)
    (evaluation evaluation_target : Choice → Real)
    (evaluation_map : ∀ a,
      evaluation_target ((R.input.labelledKummer c).map a) = evaluation a)
    (evaluation_inverse : ∀ b,
      evaluation ((R.input.labelledKummer c).inverse b) = evaluation_target b)
    (q_log : Choice → Real)
    (q_log_map : ∀ a,
      q_log ((R.input.labelledKummer c).inverse
        ((R.input.labelledKummer c).map a)) = q_log a) :
    (S3129KummerBoundaryOfActual R c evaluation evaluation_target
        evaluation_map evaluation_inverse q_log q_log_map).q_parameter =
      R.packet.determinant c := rfl

/-- The degree round trip of the actual boundary is the source arrow's
`label_map` law, so the labelled transport is genuine and not assumed. -/
theorem S3129_kummer_degree_round_trip
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) (c : Choice)
    (evaluation evaluation_target : Choice → Real)
    (evaluation_map : ∀ a,
      evaluation_target ((R.input.labelledKummer c).map a) = evaluation a)
    (evaluation_inverse : ∀ b,
      evaluation ((R.input.labelledKummer c).inverse b) = evaluation_target b)
    (q_log : Choice → Real)
    (q_log_map : ∀ a,
      q_log ((R.input.labelledKummer c).inverse
        ((R.input.labelledKummer c).map a)) = q_log a) (a : Choice) :
    (S3129KummerBoundaryOfActual R c evaluation evaluation_target
        evaluation_map evaluation_inverse q_log q_log_map).degree_inverse
        ((S3129KummerBoundaryOfActual R c evaluation evaluation_target
          evaluation_map evaluation_inverse q_log q_log_map).correspondence.map a) =
      (S3129KummerBoundaryOfActual R c evaluation evaluation_target
        evaluation_map evaluation_inverse q_log q_log_map).degree a :=
  (R.input.labelledKummer c).label_map a

#check S3129PermutationBoundaryOf
#check S3129GenericPermutationActual
#check S3129LabelledKummerActual
#check S3129KummerBoundaryOfActual

end LeanFormal.IUT.XiFPaper.S3129SourceP2BoundariesActual

end
