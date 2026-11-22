import tmp.sheaf.xif.paper.S3134FourthJointQThetaActual

/-!
# S3134: the shared qualified input of the fourth joint (exact missing link)

IUT III, Corollary 3.12 works over one qualified initial Theta-data: the
Theorem 3.11 output / descent / SHE / hull+det side and the theta-link /
1-column / IPL side are data over the *same* qualified input.

In the tree the fourth joint is expressed over two independent records:

* `I : Input Label Choice` (source input of Theorem 3.11; field
  `I.initial : InitialThetaInput I.labelPrime`);
* `J : OriginalInput l V` (theta-link / 1-column input; field
  `J.initialThetaInput : InitialThetaInput l`).

No declaration of the tree identifies these two initial Theta inputs (they are
different records, and the fourth-joint files carry both as independent
parameters).  The exact shared-input source identification is recorded here as
a structure -- one equality of prime labels plus a heterogeneous equality of
the initial Theta inputs, the same form as the
`SourceCompletionK1K2Wiring.initial_alignment` field -- and the fourth-joint
readouts are conditional on it.  It is a named missing source identification,
not a `True` marker and not an arbitrary carrier; no inequality is judged.
WRITE-ONLY: no lake/lean.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

namespace LeanFormal.IUT.XiFPaper.S3134FourthJointSharedInputActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
/- The initial Theta data of the two records must live in one universe for the
heterogeneous equality of the shared-input record; this is a universe
specialization of the shared input, not a mathematical restriction. -/
variable (J : OriginalInput.{u, uv, upi, umon, ui} l V)

/-- Exact shared qualified input of the fourth joint: the source input's prime
label and initial Theta input are those of the original-input side. -/
structure S3134FourthJointSharedInput : Prop where
  /-- The same prime label on both sides. -/
  label_eq : I.labelPrime = l
  /-- The same initial Theta data on both sides, as a heterogeneous equality
  (the two records carry it at the same value, at possibly different label
  indices before the identification). -/
  initial_heq : HEq I.initial (J.initialThetaInput)

/-- Projection: the shared prime label. -/
theorem S3134FourthJointSharedInput_label
    (S : S3134FourthJointSharedInput (I := I) (J := J)) :
    I.labelPrime = l :=
  S.label_eq

/-- Projection: the shared initial Theta input. -/
theorem S3134FourthJointSharedInput_initial
    (S : S3134FourthJointSharedInput (I := I) (J := J)) :
    HEq I.initial (J.initialThetaInput) :=
  S.initial_heq

/-- The exact data of the shared-input identification, exposed for consumers of
the fourth joint (the q/Theta readouts are data over the same qualified
input); the identification itself stays a hypothesis. -/
theorem S3134FourthJointSharedInput_data
    (S : S3134FourthJointSharedInput (I := I) (J := J)) :
    I.labelPrime = l ∧ HEq I.initial (J.initialThetaInput) :=
  ⟨S.label_eq, S.initial_heq⟩

#check S3134FourthJointSharedInput
#check S3134FourthJointSharedInput_label
#check S3134FourthJointSharedInput_initial
#check S3134FourthJointSharedInput_data

end LeanFormal.IUT.XiFPaper.S3134FourthJointSharedInputActual
