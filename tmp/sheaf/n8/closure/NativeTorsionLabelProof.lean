import tmp.sheaf.n8.closure.NativeTorsionProof
import tmp.sheaf.n8.closure.NativeSourceTorsionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
# Deep proof attempt: native torsion label and compatibility

Task-533 tries to construct

  torsionLabel : Multiplicative (A.curve.LTorsion l) -> Fin 6

and prove sixTorsionIndependent / lTorsionCompatible from actual
SignedLabel/torsion-representation/kernel-field data in SourceClauseC or the
native tuple.

The source audit is negative:

* SourceClauseC (SourceDefinition31Quantifiers.lean:1598-1637) supplies:
  torsion23_rational;
  torsion_module_basis : (Fin 2 -> ZMod l) = LTorsion l;
  canonical Galois representation;
  standard_SL2_image and image_contains_SL2;
  K_kernel_field_compatibility and kernel_field_finite_galois.
  It does NOT supply a map LTorsion -> Fin 6, a six-torsion independence
  proposition, or a q-parameter/l-torsion compatibility proposition.

* SignedLabel (Foundations/Theta/GaussianKernel.lean:94) is an integer interval
  subtype used for theta labels; it is not a six-slot torsion label and is not
  a map from LTorsion.

* Torsion23Rational (Foundations/Geometry/EllipticTorsion.lean:51-53) is the
  assertion that every 6-torsion closure point descends to the base; it is a
  rationality statement, not an enumeration/label map and not six-torsion
  independence.

* The torsion representation is a homomorphism to GL_2(ZMod l); its entries
  are coefficients in ZMod l, not a Fin 6 label of the l-torsion subgroup.

* kernel_field data in ClauseC are compatibility/finiteness propositions, not
  the label or the two opaque torsion properties.

* SourceTorsionClause (SourceDefinition31Boundary.lean:203-219) has
  torsionLabel, sixTorsionIndependent, lTorsionCompatible as source fields with
  proofs, but it is not constructed from ClauseC; the native clause has no
  identification of its abstract torsionCarrier with Multiplicative LTorsion.

Exact missing source fields (no production theorem supplies them):

  torsionLabel : Multiplicative (A.curve.LTorsion l) -> Fin 6
  sixTorsionIndependent : Prop, with proof
  lTorsionCompatible : Prop, with proof

This file reuses the existing exact NativeSourceTorsionGaps and writes the
conditional constructor only.  No arbitrary label, placeholder Prop, True,
PUnit, axiom or sorry is used.  No native label is fitted by coefficient
reduction: that would not be the source six-slot label.
-/

noncomputable section
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.InitialThetaSource.NativeTorsionLabelProof

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}

/-- The exact source-field package for the torsion label and the two
compatibility propositions.  This is the existing NativeSourceTorsionGaps,
re-exported with an explicit label-focused name. -/
abbrev TorsionLabelSourceFields (D : SourceClauseC A S C B) : Type _ :=
  NativeSourceTorsionGaps D

/-- The actual l-torsion carrier used by the label field. -/
abbrev TorsionLabelCarrier : Type u :=
  Multiplicative (A.curve.LTorsion l)

/-- Constructor from the exact primitive fields.  The fields are explicit;
nothing is derived from ClauseC's torsion basis or representation. -/
noncomputable def sourceTorsionClauseOfFields
    (D : SourceClauseC A S C B) (F : TorsionLabelSourceFields D) :
    SourceTorsionClause l :=
  F.toSourceTorsionClause

/-- Projection: the constructed source torsion clause uses the supplied label. -/
theorem sourceTorsionClauseOfFields_label
    (D : SourceClauseC A S C B) (F : TorsionLabelSourceFields D) :
    (sourceTorsionClauseOfFields D F).torsionLabel = F.torsionLabel := rfl

/-- Projection: the constructed source torsion clause uses the supplied
six-torsion proposition. -/
theorem sourceTorsionClauseOfFields_six
    (D : SourceClauseC A S C B) (F : TorsionLabelSourceFields D) :
    (sourceTorsionClauseOfFields D F).sixTorsionIndependent =
      F.sixTorsionIndependent := rfl

/-- Projection: the constructed source torsion clause uses the supplied
l-torsion compatibility proposition. -/
theorem sourceTorsionClauseOfFields_l
    (D : SourceClauseC A S C B) (F : TorsionLabelSourceFields D) :
    (sourceTorsionClauseOfFields D F).lTorsionCompatible =
      F.lTorsionCompatible := rfl

/-- The actual ClauseC torsion basis is available, but it is a rank-two basis,
not a Fin 6 label map. -/
noncomputable def actualTorsionBasis
    (D : SourceClauseC A S C B) :
    (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l :=
  D.torsion_basis

/-- The actual ClauseC 6-torsion rationality is available, but it is a
rationality statement, not six-torsion independence. -/
theorem actualTorsion23Rational
    (D : SourceClauseC A S C B) :
    PuncturedEllipticCurve.Torsion23Rational A.curve :=
  D.torsion23_rational

/-- The actual ClauseC canonical representation is available, but it maps to
GL_2(ZMod l), not to a Fin 6 label. -/
noncomputable def actualRepresentation
    (D : SourceClauseC A S C B) :
    (AlgebraicClosure A.F ≃ₐ[A.F] AlgebraicClosure A.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  D.galois_representation

/-- Exact missing primitive report: the label and the two propositions are
still explicit source fields.  No derivation from SignedLabel, torsion basis,
torsion23_rational, the GL_2 representation, or kernel-field data is present. -/
structure NativeTorsionLabelMissing
    (D : SourceClauseC A S C B) where
  torsionLabel : TorsionLabelCarrier (A := A) (l := l) -> Fin 6
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

/-- The missing package is definitionally the existing source-field package. -/
def NativeTorsionLabelMissing.toFields
    {D : SourceClauseC A S C B} (M : NativeTorsionLabelMissing D) :
    TorsionLabelSourceFields D where
  torsionLabel := M.torsionLabel
  sixTorsionIndependent := M.sixTorsionIndependent
  sixTorsionIndependent_proved := M.sixTorsionIndependent_proved
  lTorsionCompatible := M.lTorsionCompatible
  lTorsionCompatible_proved := M.lTorsionCompatible_proved

/-- Conditional construction of the source torsion clause from the exact
missing package. -/
noncomputable def NativeTorsionLabelMissing.toSourceTorsionClause
    {D : SourceClauseC A S C B} (M : NativeTorsionLabelMissing D) :
    SourceTorsionClause l :=
  sourceTorsionClauseOfFields D M.toFields

/-- Exact status theorem: only the actual ClauseC basis/rationality/
representation are derived; the label and the two propositions are supplied
by the missing package, not proved from ClauseC. -/
theorem nativeTorsionLabelStatus
    (D : SourceClauseC A S C B) (M : NativeTorsionLabelMissing D) :
    PuncturedEllipticCurve.Torsion23Rational A.curve ∧
      (Nonempty ((Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value]
        A.curve.LTorsion l)) ∧
      ((NativeTorsionLabelMissing.toSourceTorsionClause M).torsionLabel =
        M.torsionLabel) ∧
      ((NativeTorsionLabelMissing.toSourceTorsionClause M).sixTorsionIndependent =
        M.sixTorsionIndependent) ∧
      ((NativeTorsionLabelMissing.toSourceTorsionClause M).lTorsionCompatible =
        M.lTorsionCompatible) :=
  ⟨actualTorsion23Rational D, ⟨actualTorsionBasis D⟩,
    sourceTorsionClauseOfFields_label D M.toFields,
    sourceTorsionClauseOfFields_six D M.toFields,
    sourceTorsionClauseOfFields_l D M.toFields⟩

end LeanFormal.IUT.InitialThetaSource.NativeTorsionLabelProof
