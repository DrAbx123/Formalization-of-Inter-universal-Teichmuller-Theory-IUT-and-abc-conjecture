import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual F_l^x action on the Theta-pilot image index

IUT III, Step (xi) / Corollary 3.12: the Theta-pilot procession is indexed by
F_l^x (the signed label set F_l^star), and the theta values carry that index.

This file constructs the actual multiplicative action of the unit group
(Fl l.value)^x on:

* the signed label type SignedLabel l.value, via the actual equivalence
  SignedLabel.equiv and multiplication in Fl l.value;
* the Theta-pilot image index ThetaPilotCarrier l * SignedLabel l.value.

The action is defined by actual multiplication in the finite field, not by an
arbitrary cardinality equivalence. Unit and multiplication laws are proved.

No source theorem identifying this algebraic index action with the paper's
Galois action on Theta-pilot objects is asserted; that identification is a
separate source comparison.

No empty type, True, PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe uv

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}

/-- The actual Theta-pilot image index: processions times signed labels. -/
abbrev ThetaPilotImageIndex (l : PrimeGeFive) : Type :=
  ThetaPilotCarrier l × SignedLabel l.value

/-- The actual action of a unit of Fl l on a signed label: multiply through
the actual SignedLabel/Fl equivalence. -/
noncomputable def flUnitsSmulLabel
    (u : (Fl l.value)ˣ) (j : SignedLabel l.value) :
    SignedLabel l.value :=
  (SignedLabel.equiv l).symm
    ((u : Fl l.value) * (SignedLabel.equiv l j))

/-- The unit of the multiplicative group acts by the identity on labels. -/
theorem flUnitsSmulLabel_one (j : SignedLabel l.value) :
    flUnitsSmulLabel (1 : (Fl l.value)ˣ) j = j := by
  show (SignedLabel.equiv l).symm
      ((1 : Fl l.value) * (SignedLabel.equiv l j)) = j
  rw [one_mul]
  exact (SignedLabel.equiv l).symm_apply_apply j

/-- The action is multiplicative. -/
theorem flUnitsSmulLabel_mul
    (u v : (Fl l.value)ˣ) (j : SignedLabel l.value) :
    flUnitsSmulLabel (u * v) j =
      flUnitsSmulLabel u (flUnitsSmulLabel v j) := by
  unfold flUnitsSmulLabel
  simp only [Units.val_mul, mul_assoc, Equiv.apply_symm_apply]

/-- The actual F_l^x action on the Theta-pilot image index. -/
noncomputable def flUnitsActOnThetaPilotIndex
    (u : (Fl l.value)ˣ) :
    ThetaPilotImageIndex l → ThetaPilotImageIndex l :=
  fun idx => (idx.1, flUnitsSmulLabel u idx.2)

/-- The Theta-pilot index action is the identity at the unit. -/
theorem flUnitsActOnThetaPilotIndex_one
    (idx : ThetaPilotImageIndex l) :
    flUnitsActOnThetaPilotIndex (1 : (Fl l.value)ˣ) idx = idx := by
  unfold flUnitsActOnThetaPilotIndex
  cases idx with
  | mk n j =>
    simp [flUnitsSmulLabel_one]

/-- The Theta-pilot index action is multiplicative. -/
theorem flUnitsActOnThetaPilotIndex_mul
    (u v : (Fl l.value)ˣ) (idx : ThetaPilotImageIndex l) :
    flUnitsActOnThetaPilotIndex (u * v) idx =
      flUnitsActOnThetaPilotIndex u (flUnitsActOnThetaPilotIndex v idx) := by
  unfold flUnitsActOnThetaPilotIndex
  cases idx with
  | mk n j =>
    simp [flUnitsSmulLabel_mul]

/-- The actual F_l^x action data on the Theta-pilot image index. -/
structure FlUnitsThetaPilotActionData where
  smul : (Fl l.value)ˣ → ThetaPilotImageIndex l → ThetaPilotImageIndex l
  one_smul : ∀ idx, smul 1 idx = idx
  mul_smul : ∀ (u v : (Fl l.value)ˣ) (idx : ThetaPilotImageIndex l),
    smul (u * v) idx = smul u (smul v idx)

/-- The actual F_l^x action from finite-field multiplication. -/
noncomputable def actualFlUnitsThetaPilotAction :
    FlUnitsThetaPilotActionData (l := l) where
  smul := flUnitsActOnThetaPilotIndex
  one_smul := flUnitsActOnThetaPilotIndex_one
  mul_smul := flUnitsActOnThetaPilotIndex_mul

/-- The actual action's smul is the finite-field multiplier. -/
theorem actualFlUnitsThetaPilotAction_smul
    (u : (Fl l.value)ˣ) (idx : ThetaPilotImageIndex l) :
    (actualFlUnitsThetaPilotAction (l := l)).smul u idx =
      (idx.1, flUnitsSmulLabel u idx.2) :=
  rfl

end LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual

end
