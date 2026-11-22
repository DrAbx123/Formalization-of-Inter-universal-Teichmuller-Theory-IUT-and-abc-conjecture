/-! DEPRECATED: the six-slot corrected torsion path is
`tmp.sheaf.xif.paper.NativeSourceTorsionGapsActualConstruction` with carrier
`rootsOfUnity 6` and the primitive-root label. This legacy module uses the old
l-torsion label domain and is not imported by the corrected path. -/

import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply
import tmp.sheaf.n8.closure.NativeSourceTorsionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Native torsion fields: derivation attempt and exact primitive fields

Task-510 bottom-up derivation attempt.

Inputs read:
* SourceClauseC (SourceDefinition31Quantifiers.lean): native torsion basis,
  canonical matrix representation, its literal SL2 containment, and the
  kernel-field identification;
* NativeSourceTorsionActual.lean: the native SourceTorsionClause construction
  through SourceTorsionDatum.ofSourceClauseC and
  D5TorsionSupply.toTorsionClause.

Result: the actual carrier, representation, range, surjectivity, and
imageContainsSL2 proof are derived from clause (c). The three remaining
SourceTorsionClause fields are NOT determined by SourceClauseC:

1. torsionLabel : Multiplicative (A.curve.LTorsion l) -> Fin 6.
   SourceClauseC provides a rank-two l-torsion basis, not a six-slot
   labelling. No native six-slot label map occurs in the clause-c or Tate
   fields. A label map is an additional source primitive.
2. sixTorsionIndependent : Prop and its proof.
   SourceClauseC provides torsion23_rational, which is a rationality
   statement, not six-torsion independence. No implication is available.
3. lTorsionCompatible : Prop and its proof.
   SourceClauseC contains no q-parameter/l-torsion compatibility statement.

This file therefore packages exactly those three primitives explicitly. It
does not invent a label, does not replace the propositions by a placeholder,
and does not assert an inhabitant. The primitive package may be supplied by a
later source task; the conditional constructor is the strongest bottom-up
result available here.
-/

noncomputable section

namespace LeanFormal.IUT
namespace InitialThetaSource
namespace NativeTorsionFields

open NativeSourceTorsion

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}

/-- The corrected six-slot torsion carrier. -/
abbrev NativeTorsionCarrier : Type u :=
  nativeTorsionCarrier (A := A) (l := l)

/-- The exact primitive fields that are not derivable from SourceClauseC. -/
structure NativeTorsionPrimitiveFields
    (D : SourceClauseC A S C B) where
  /-- The six-slot labelling of the actual l-torsion carrier. -/
  torsionLabel : nativeTorsionCarrier (A := A) (l := l) → Fin 6
  /-- Six-torsion independence: a source condition, not clause-c data. -/
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  /-- l-torsion/q-compatibility: a source condition, not clause-c data. -/
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

/-- The actual clause-(c) torsion datum (rank-two basis, literal SL2
containment, kernel-field identification). This is derived directly from the
native clause and reuses SourceTorsionDatum.ofSourceClauseC. -/
noncomputable def clauseTorsionDatum
    (D : SourceClauseC A S C B) :
    TorsionCarrierReduction.SourceTorsionDatum l A :=
  NativeSourceTorsion.nativeTorsionDatum D

/-- The conditional SourceTorsionClause built from the primitive fields and
the actual clause-(c) datum, reusing the existing D5 bridge. -/
noncomputable def SourceTorsionClauseOfPrimitives
    (D : SourceClauseC A S C B) (F : NativeTorsionPrimitiveFields D) :
    Theorem311Source.SourceTorsionClause l :=
  NativeSourceTorsion.nativeSourceTorsionClause D F.torsionLabel
    F.sixTorsionIndependent F.sixTorsionIndependent_proved
    F.lTorsionCompatible F.lTorsionCompatible_proved

/-- The constructed clause has the actual l-torsion carrier. -/
theorem SourceTorsionClauseOfPrimitives_torsionCarrier
    (D : SourceClauseC A S C B) (F : NativeTorsionPrimitiveFields D) :
    (SourceTorsionClauseOfPrimitives D F).torsionCarrier =
      nativeTorsionCarrier (A := A) (l := l) := rfl

/-- The constructed clause has exactly the supplied label primitive. -/
theorem SourceTorsionClauseOfPrimitives_torsionLabel
    (D : SourceClauseC A S C B) (F : NativeTorsionPrimitiveFields D) :
    (SourceTorsionClauseOfPrimitives D F).torsionLabel = F.torsionLabel := rfl

/-- The constructed clause has exactly the supplied six-torsion primitive. -/
theorem SourceTorsionClauseOfPrimitives_six
    (D : SourceClauseC A S C B) (F : NativeTorsionPrimitiveFields D) :
    (SourceTorsionClauseOfPrimitives D F).sixTorsionIndependent =
      F.sixTorsionIndependent := rfl

/-- The constructed clause has exactly the supplied l-torsion primitive. -/
theorem SourceTorsionClauseOfPrimitives_l
    (D : SourceClauseC A S C B) (F : NativeTorsionPrimitiveFields D) :
    (SourceTorsionClauseOfPrimitives D F).lTorsionCompatible =
      F.lTorsionCompatible := rfl

/-- The primitive package recovered from the constructed clause. This
records the interface boundary: they are fields of the target clause, not
consequences of SourceClauseC. -/
noncomputable def primitivesOfBuiltClause
    (D : SourceClauseC A S C B) (F : NativeTorsionPrimitiveFields D) :
    NativeTorsionPrimitiveFields D where
  torsionLabel := (SourceTorsionClauseOfPrimitives D F).torsionLabel
  sixTorsionIndependent := (SourceTorsionClauseOfPrimitives D F).sixTorsionIndependent
  sixTorsionIndependent_proved :=
    (SourceTorsionClauseOfPrimitives D F).sixTorsionIndependent_proved
  lTorsionCompatible := (SourceTorsionClauseOfPrimitives D F).lTorsionCompatible
  lTorsionCompatible_proved :=
    (SourceTorsionClauseOfPrimitives D F).lTorsionCompatible_proved

/-- The primitive package recovered from the constructed clause is the
original package. -/
theorem primitivesOfBuiltClause_sourceTorsionClauseOfPrimitives
    (D : SourceClauseC A S C B) (F : NativeTorsionPrimitiveFields D) :
    primitivesOfBuiltClause D F = F := by
  cases F
  rfl

/-- The actual clause-(c) l-torsion basis remains available. -/
noncomputable def clauseTorsionBasis
    (D : SourceClauseC A S C B) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l :=
  D.torsion_basis

/-- The actual clause-(c) two-star-three torsion rationality remains available,
but it is not the six-torsion independence primitive. -/
theorem clauseTorsion23Rational
    (D : SourceClauseC A S C B) :
    PuncturedEllipticCurve.Torsion23Rational A.curve :=
  D.torsion23_rational

/-- The actual canonical representation of clause (c) remains available. -/
noncomputable def clauseRepresentation
    (D : SourceClauseC A S C B) :
    SourceAbsoluteGalois A →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  D.representation

/-- The literal SL2 containment of clause (c). -/
theorem clauseImageContainsSL2
    (D : SourceClauseC A S C B) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      D.representation.range :=
  D.image_contains_SL2

/-- Exact derivation status:

* the actual carrier, D5 datum, canonical representation, range, surjectivity,
  and imageContainsSL2 are derived from SourceClauseC (through
  NativeSourceTorsionActual);
* torsionLabel, sixTorsionIndependent, and lTorsionCompatible are not derived;
  they are the primitive fields of NativeTorsionPrimitiveFields.

This theorem is a conjunction of the available actual facts and the explicit
primitive package. It is not an unconditional SourceTorsionClause. -/
theorem nativeTorsionDerivationStatus
    (D : SourceClauseC A S C B) (F : NativeTorsionPrimitiveFields D) :
    (PuncturedEllipticCurve.Torsion23Rational A.curve) ∧
      (Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
        D.representation.range) ∧
      ((SourceTorsionClauseOfPrimitives D F).torsionLabel = F.torsionLabel) ∧
      ((SourceTorsionClauseOfPrimitives D F).sixTorsionIndependent =
        F.sixTorsionIndependent) ∧
      ((SourceTorsionClauseOfPrimitives D F).lTorsionCompatible =
        F.lTorsionCompatible) :=
  ⟨clauseTorsion23Rational D, clauseImageContainsSL2 D,
    SourceTorsionClauseOfPrimitives_torsionLabel D F,
    SourceTorsionClauseOfPrimitives_six D F,
    SourceTorsionClauseOfPrimitives_l D F⟩

end NativeTorsionFields
end InitialThetaSource
end LeanFormal.IUT

end
