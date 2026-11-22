/-! DEPRECATED: the six-slot corrected torsion path is
`tmp.sheaf.xif.paper.NativeSourceTorsionGapsActualConstruction` with carrier
`rootsOfUnity 6` and the primitive-root label. This legacy module uses the old
l-torsion label domain and is not imported by the corrected path. -/

import tmp.sheaf.n8.closure.PaperDonorsConstructed2
import tmp.sheaf.n8.closure.NativeSourceTorsionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

/-!
# Actual native torsion fields from the source clause data

Task-656 attempts the three SourceTorsionClause fields

  torsionLabel : Multiplicative (S.candidate.arithmetic.curve.LTorsion l) -> Fin 6
  sixTorsionIndependent : Prop, with proof
  lTorsionCompatible : Prop, with proof

from the actual SourceInitialThetaData/ClauseC torsion representation.

Actual construction:

* lTorsionCompatible: the literal clause (c) condition
  l_prime_to_bad_residue_characteristics is projected by
  PaperDonorsConstructed2.paperLTorsionCompatible / _proved.  This is the actual
  l-coprime-to-bad-residue compatibility proposition and its source proof, not
  an arbitrary placeholder.

Still missing:

* torsionLabel: ClauseC supplies a rank-two l-torsion basis
  (Fin 2 -> ZMod l) = LTorsion l, not a six-slot label map LTorsion -> Fin 6;
  no source lemma provides the label.
* sixTorsionIndependent: ClauseC supplies torsion23_rational (6-torsion
  descends), not an independence statement; no proof is available.

This file constructs the actual lTorsionCompatible field and the conditional
partial field package; it records the exact missing label/independence object.
No arbitrary label/Prop/True/PUnit/axiom/sorry is used.  WRITE-ONLY;
compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeTorsionFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.PaperDonorsConstructed2
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}
variable (S : SourceInitialThetaData.{u} l)

/-- The actual l-torsion carrier of the source arithmetic curve. -/
abbrev NativeTorsionCarrier : Type u :=
  nativeTorsionCarrier (A := S.candidate.arithmetic) (l := l)

/-- The actual clause (c) l-torsion compatibility proposition: l is coprime to
every bad residue characteristic. -/
def nativeLTorsionCompatible : Prop :=
  paperLTorsionCompatible S

/-- The actual clause (c) proof of l-torsion compatibility. -/
theorem nativeLTorsionCompatible_proved :
    nativeLTorsionCompatible (S := S) :=
  paperLTorsionCompatible_proved S

/-! ## 1. Exact missing label and six-torsion independence -/

/-- The exact missing six-slot label on the actual l-torsion carrier. -/
def MissingTorsionLabel : Prop :=
  NativeTorsionCarrier (S := S) -> Fin 6

/-- The exact missing six-torsion independence proposition with proof. -/
structure MissingSixTorsionIndependent where
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent

/-- The actual partial field package: lTorsionCompatible is actual clause (c)
data; label and six-torsion independence are explicit missing fields. -/
structure NativeTorsionFieldsPartial where
  torsionLabel : NativeTorsionCarrier (S := S) -> Fin 6
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent

/-! ## 2. Actual ClauseC data -/

/-- The actual ClauseC l-torsion basis. -/
noncomputable def nativeTorsionBasis :
    (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value]
      S.candidate.arithmetic.curve.LTorsion l :=
  S.clauseC.torsion_basis

/-- The actual ClauseC torsion23 rationality. -/
theorem nativeTorsion23Rational :
    PuncturedEllipticCurve.Torsion23Rational S.candidate.arithmetic.curve :=
  S.clauseC.torsion23_rational

/-- The actual ClauseC canonical representation. -/
noncomputable def nativeTorsionRepresentation :
    (AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  S.clauseC.galois_representation

/-- The actual ClauseC literal SL2 containment. -/
theorem nativeTorsionImageContainsSL2 :
    S.clauseC.standard_SL2_image ≤ S.clauseC.galois_representation.range :=
  S.clauseC.image_contains_SL2

/-! ## 3. Conditional object and exact missing package -/

/-- Exact missing package for the unconditional native torsion fields. -/
def MissingNativeTorsionFields : Prop :=
  Nonempty (NativeTorsionFieldsPartial (S := S))

/-- The missing package is exactly the partial field structure. -/
theorem missingNativeTorsionFields_iff :
    MissingNativeTorsionFields (S := S) ↔
      Nonempty (NativeTorsionFieldsPartial (S := S)) := Iff.rfl

/-- Actual conjunction of the available ClauseC data and the actual
lTorsionCompatible field.  This does not assert the missing label or six-torsion
independence. -/
theorem nativeTorsionActualStatus :
    PuncturedEllipticCurve.Torsion23Rational S.candidate.arithmetic.curve ∧
      (Nonempty ((Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value]
        S.candidate.arithmetic.curve.LTorsion l)) ∧
      (S.clauseC.standard_SL2_image ≤ S.clauseC.galois_representation.range) ∧
      nativeLTorsionCompatible (S := S) :=
  ⟨nativeTorsion23Rational S, ⟨nativeTorsionBasis S⟩,
    nativeTorsionImageContainsSL2 S, nativeLTorsionCompatible_proved S⟩

end LeanFormal.IUT.XiFPaper.NativeTorsionFieldsActual
