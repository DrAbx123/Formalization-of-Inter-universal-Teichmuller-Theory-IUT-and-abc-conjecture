/-! DEPRECATED: the six-slot corrected torsion path is
`tmp.sheaf.xif.paper.NativeSourceTorsionGapsActualConstruction` with carrier
`rootsOfUnity 6` and the primitive-root label. This legacy module uses the old
l-torsion label domain and is not imported by the corrected path. -/

import tmp.sheaf.xif.paper.NativeTorsionFieldsActualAdapted
import tmp.sheaf.n8.closure.PaperDonorsConstructed2
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

/-!
# Complete native torsion fields: construction attempt

Task-663 attempts

  torsionLabel : Multiplicative (LTorsion l) -> Fin 6
  sixTorsionIndependent : Prop, with proof

from the actual ClauseC torsion basis and 6-torsion descent data.

Actual data available:

* lTorsionCompatible is already actual: the literal ClauseC condition
  l_prime_to_bad_residue_characteristics, with its proof (task-656);
* torsion_module_basis : (Fin 2 -> ZMod l) = LTorsion l;
* torsion23_rational : Torsion23Rational curve, i.e. every 6-torsion closure
  point descends to the base.  This is a descent/rationality statement, not an
  enumeration of six points and not an independence statement.

Not derivable:

* torsionLabel: the rank-two l-torsion basis does not give a six-slot label map
  LTorsion -> Fin 6.  No source lemma, finite enumeration, or canonical six
  generators exist in ClauseC.
* sixTorsionIndependent: Torsion23Rational is a descent statement; it does not
  provide a proposition with a proof of six-torsion independence.  No such
  source object occurs in ClauseC.

This file packages the actual lTorsion field and the actual 6-torsion descent
data, then records the exact missing source object.  No arbitrary label or
independence placeholder is introduced.  No inequality judgment.
WRITE-ONLY; compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeTorsionFieldsCompleteAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.PaperDonorsConstructed2
open LeanFormal.IUT.XiFPaper.NativeTorsionFieldsActualAdapted
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}
variable (S : SourceInitialThetaData.{u} l)

/-- The actual l-torsion compatibility field from ClauseC. -/
def completeLTorsionCompatible : Prop :=
  nativeLTorsionCompatible (S := S)

/-- The actual proof of the lTorsionCompatible field. -/
theorem completeLTorsionCompatible_proved :
    completeLTorsionCompatible (S := S) :=
  nativeLTorsionCompatible_proved S

/-- The actual ClauseC torsion basis. -/
noncomputable def completeTorsionBasis :
    (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value]
      S.candidate.arithmetic.curve.LTorsion l :=
  nativeTorsionBasis S

/-- The actual ClauseC 6-torsion descent/rationality statement. -/
theorem completeTorsion23Descent :
    PuncturedEllipticCurve.Torsion23Rational S.candidate.arithmetic.curve :=
  nativeTorsion23Rational S

/-! ## 1. Exact missing source object -/

/-- The exact missing label map on the actual l-torsion carrier. -/
def MissingTorsionLabelComplete : Prop :=
  NativeTorsionCarrier (S := S) -> Fin 6

/-- The exact missing six-torsion independence proposition and proof. -/
structure MissingSixTorsionIndependentComplete where
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent

/-- The exact missing source package for the two fields. -/
structure MissingNativeTorsionFieldsCompleteAdapted where
  torsionLabel : NativeTorsionCarrier (S := S) -> Fin 6
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent

/-- No complete package is asserted; its exact shape is the missing object. -/
def MissingNativeTorsionFieldsCompleteAdaptedProp : Prop :=
  Nonempty (MissingNativeTorsionFieldsCompleteAdapted (S := S))

/-! ## 2. What is actual and what remains -/

/-- Actual status: lTorsionCompatible is constructed; the two other fields are
the explicit missing objects.  The 6-torsion descent data is available but is
not relabelled as six-torsion independence. -/
theorem nativeTorsionFieldsCompleteStatus :
    (PuncturedEllipticCurve.Torsion23Rational S.candidate.arithmetic.curve) ∧
      (Nonempty ((Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value]
        S.candidate.arithmetic.curve.LTorsion l)) ∧
      completeLTorsionCompatible (S := S) :=
  ⟨completeTorsion23Descent S, ⟨completeTorsionBasis S⟩,
    completeLTorsionCompatible_proved S⟩

/-- Exact missing label object, as a proposition. -/
def missingTorsionLabelObject : Prop :=
  MissingTorsionLabelComplete (S := S)

/-- Exact missing independence object, as a proposition. -/
def missingSixTorsionObject : Prop :=
  Nonempty (MissingSixTorsionIndependentComplete (S := S))

end LeanFormal.IUT.XiFPaper.NativeTorsionFieldsCompleteAdapted
