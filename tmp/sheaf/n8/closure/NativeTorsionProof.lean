/-! DEPRECATED: the six-slot corrected torsion path is
`tmp.sheaf.xif.paper.NativeSourceTorsionGapsActualConstruction` with carrier
`rootsOfUnity 6` and the primitive-root label. This legacy module uses the old
l-torsion label domain and is not imported by the corrected path. -/

import tmp.sheaf.n8.closure.NativeSourceTorsionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Deep proof attempt: torsion label, six-torsion independence, l-torsion compatibility

Task-523 write-only attempt.

Sources read:
* SourceDefinition31Quantifiers.lean, SourceClauseC:
  - torsion23_rational;
  - torsion_basis : (Fin 2 -> ZMod l) = LTorsion l;
  - representation and representation_eq_canonical;
  - image_contains_SL2;
  - kernel_field_identification(_range).
* SourceDefinition31Boundary.lean, SourceTorsionClause:
  - torsionCarrier, torsionLabel : carrier -> Fin 6, torsionNonempty;
  - representationCarrier/Group, representation, representation_surjective;
  - imageContainsSL2, sixTorsionIndependent, lTorsionCompatible.
* SourceDefinition31DualContractAlignment.lean:
  - the dual contract audit states that the current side has an abstract
    torsionCarrier with a Fin 6 label and opaque sixTorsionIndependent and
    lTorsionCompatible, while the legacy ClauseC has the typed torsion basis,
    rational 2*3 torsion, canonical representation, and literal SL2
    containment. The two contracts are not record-equivalent.
* NativeSourceTorsionActual.lean: the existing D5 construction, reused here.

Derived or available from the actual clause (c) datum:
* actual l-torsion carrier: Multiplicative (A.curve.LTorsion l);
* actual torsion basis D.torsion_basis;
* actual canonical representation D.representation;
* actual SL2 containment D.image_contains_SL2;
* actual torsion23_rational D.torsion23_rational.

Not derivable from the current source data:
1. torsionLabel : Multiplicative (A.curve.LTorsion l) -> Fin 6.
   ClauseC supplies a rank-two l-torsion basis, not a six-slot label map.
   No production lemma constructs a map from the l-torsion carrier to Fin 6.
2. sixTorsionIndependent : Prop and its proof.
   ClauseC supplies torsion23_rational, a rationality statement. Neither the
   dual-contract file nor the torsion carrier file proves an implication from
   rationality to six-torsion independence.
3. lTorsionCompatible : Prop and its proof.
   ClauseC contains no q-parameter/l-torsion compatibility statement; the
   dual-contract audit explicitly lists this field as opaque on the current
   side.

Therefore the three fields remain exact primitive source fields. This file
reuses the existing NativeSourceTorsionGaps and its D5-backed constructor; it
does not invent a label, does not replace a proposition by a placeholder, and
does not assert an inhabitant.
-/

noncomputable section

namespace LeanFormal.IUT.InitialThetaSource.NativeTorsionProof

open NativeSourceTorsion

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}

/-- The exact primitive fields required for the native torsion clause. This is
the existing gap ledger from NativeSourceTorsionActual, reused without change. -/
abbrev PrimitiveFields (D : SourceClauseC A S C B) : Type _ :=
  NativeSourceTorsionGaps D

/-- The conditional native SourceTorsionClause from the exact primitive fields.
This reuses NativeSourceTorsionGaps.toSourceTorsionClause and therefore the D5
constructor. -/
noncomputable def nativeSourceTorsionClauseOfPrimitives
    (D : SourceClauseC A S C B) (P : PrimitiveFields D) :
    Theorem311Source.SourceTorsionClause l :=
  P.toSourceTorsionClause

/-- Projection: the constructed clause uses the supplied torsion label. -/
theorem nativeSourceTorsionClauseOfPrimitives_label
    (D : SourceClauseC A S C B) (P : PrimitiveFields D) :
    (nativeSourceTorsionClauseOfPrimitives D P).torsionLabel =
      P.torsionLabel := rfl

/-- Projection: the constructed clause uses the supplied six-torsion
independence proposition. -/
theorem nativeSourceTorsionClauseOfPrimitives_six
    (D : SourceClauseC A S C B) (P : PrimitiveFields D) :
    (nativeSourceTorsionClauseOfPrimitives D P).sixTorsionIndependent =
      P.sixTorsionIndependent := rfl

/-- Projection: the constructed clause uses the supplied l-torsion
compatibility proposition. -/
theorem nativeSourceTorsionClauseOfPrimitives_l
    (D : SourceClauseC A S C B) (P : PrimitiveFields D) :
    (nativeSourceTorsionClauseOfPrimitives D P).lTorsionCompatible =
      P.lTorsionCompatible := rfl

/-- The actual clause-(c) torsion basis remains available. -/
noncomputable def actualTorsionBasis
    (D : SourceClauseC A S C B) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l :=
  D.torsion_basis

/-- The actual clause-(c) canonical representation remains available. -/
noncomputable def actualRepresentation
    (D : SourceClauseC A S C B) :
    SourceAbsoluteGalois A →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  D.representation

/-- The actual clause-(c) SL2 containment remains available. -/
theorem actualImageContainsSL2
    (D : SourceClauseC A S C B) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      D.representation.range :=
  D.image_contains_SL2

/-- The actual clause-(c) torsion23 rationality remains available, but it is
not the six-torsion independence field. -/
theorem actualTorsion23Rational
    (D : SourceClauseC A S C B) :
    PuncturedEllipticCurve.Torsion23Rational A.curve :=
  D.torsion23_rational

/-- Exact primitive report: no production construction of these three fields
from SourceClauseC/Torsion23Rational/LTorsion is present. This is recorded as
a structure with exactly the three source hypotheses. -/
structure NativeTorsionMissingTheorems
    (D : SourceClauseC A S C B) where
  /-- Missing: a six-slot label map on the actual l-torsion carrier. -/
  torsionLabel : nativeTorsionCarrier (A := A) (l := l) → Fin 6
  /-- Missing: a source proposition for six-torsion independence. -/
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  /-- Missing: a source proposition for q-parameter/l-torsion compatibility. -/
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

/-- The missing-theorem package is exactly the same data as the primitive gap
package; no new field is introduced. -/
def NativeTorsionMissingTheorems.toPrimitiveFields
    {D : SourceClauseC A S C B} (M : NativeTorsionMissingTheorems D) :
    PrimitiveFields D where
  torsionLabel := M.torsionLabel
  sixTorsionIndependent := M.sixTorsionIndependent
  sixTorsionIndependent_proved := M.sixTorsionIndependent_proved
  lTorsionCompatible := M.lTorsionCompatible
  lTorsionCompatible_proved := M.lTorsionCompatible_proved

/-- The missing-theorem package yields the native torsion clause only through
the explicit D5 constructor, not by a derivation from clause C. -/
noncomputable def NativeTorsionMissingTheorems.toSourceTorsionClause
    {D : SourceClauseC A S C B} (M : NativeTorsionMissingTheorems D) :
    Theorem311Source.SourceTorsionClause l :=
  nativeSourceTorsionClauseOfPrimitives D M.toPrimitiveFields

/-- Exact status: the three fields are not produced by source data; they are
explicit primitives. The actual torsion basis, representation, SL2 containment,
and torsion23 rationality are produced by SourceClauseC. -/
theorem nativeTorsionProofStatus
    (D : SourceClauseC A S C B) (M : NativeTorsionMissingTheorems D) :
    (PuncturedEllipticCurve.Torsion23Rational A.curve) ∧
      (Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
        D.representation.range) ∧
      ((NativeTorsionMissingTheorems.toSourceTorsionClause M).torsionLabel =
        M.torsionLabel) ∧
      ((NativeTorsionMissingTheorems.toSourceTorsionClause M).sixTorsionIndependent =
        M.sixTorsionIndependent) ∧
      ((NativeTorsionMissingTheorems.toSourceTorsionClause M).lTorsionCompatible =
        M.lTorsionCompatible) :=
  ⟨actualTorsion23Rational D, actualImageContainsSL2 D,
    nativeSourceTorsionClauseOfPrimitives_label D M.toPrimitiveFields,
    nativeSourceTorsionClauseOfPrimitives_six D M.toPrimitiveFields,
    nativeSourceTorsionClauseOfPrimitives_l D M.toPrimitiveFields⟩

end LeanFormal.IUT.InitialThetaSource.NativeTorsionProof

end
