import tmp.sheaf.xif.paper.S3139FieldCArchimedeanBundleActual
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: C1 — the source infinite-place choice is actual and exists (no longer missing)

C1 of the first-triangle residual was the source infinite-place choice
`SourceInfinitePlaceChoice` for the archimedean realification
(IUT III:616-620).  Mathlib proves that every number field has infinite places
(embeddings into an algebraically closed field and `InfinitePlace.nonempty`);
since the actual `F_mod` is a number field, the choice exists.  This file:

* proves `sourceInfinitePlaceChoice_nonempty`: the choice datum is inhabited;
* constructs `sourceInfinitePlaceChoiceActual` by classical choice;
* instantiates the actual archimedean character and the
  `SourceArchimedeanRealification` bundle with NO supplied data:
  `sourceArchimedeanRealification_nonempty`.

Honest status: the archimedean realified scalar channel needs only an
archimedean place (real or complex; the completion norm-log is real in both
cases), which exists for every number field.  If a downstream consumer needs a
*specific* infinite place, that selection is a separate canonical-choice datum;
the existence of the channel is not missing data.  The earlier "real place"
formulation was a modeling convention.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C1InfinitePlaceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanBundleActual

universe u

/-- Every choice datum of an infinite place of the actual `F_mod` exists
(Mathlib: number fields have infinite places). -/
theorem sourceInfinitePlaceChoice_nonempty
    (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l) :
    Nonempty (SourceInfinitePlaceChoice A) := by
  haveI : Nonempty (NumberField.InfinitePlace A.Fmod) := inferInstance
  exact ‹Nonempty (NumberField.InfinitePlace A.Fmod)›

/-- The actual infinite place of the actual `F_mod`, by classical choice from
the Mathlib existence theorem. -/
noncomputable def sourceInfinitePlaceChoiceActual
    (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l) :
    SourceInfinitePlaceChoice A :=
  Classical.choice (sourceInfinitePlaceChoice_nonempty A)

/-- The actual Real scalar character of the copies with no supplied data. -/
noncomputable def sourceArchimedeanScalarActual
    (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l) :
    (A.Fmod)ˣ →* ℝˣ :=
  sourceInfinitePlaceScalarCharacter A (sourceInfinitePlaceChoiceActual A)

/-- The archimedean realification bundle exists with no supplied data (C1 is
discharged at the component level; the place is a classical choice). -/
theorem sourceArchimedeanRealification_nonempty
    (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l) :
    Nonempty (SourceArchimedeanRealification A) :=
  ⟨SourceArchimedeanRealification.ofChoice A
    (sourceInfinitePlaceChoiceActual A)⟩

/-- The actual archimedean scalar character is multiplicative (consumer form,
again with no supplied choice). -/
theorem sourceArchimedeanScalarActual_mul
    (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l)
    (a b : (A.Fmod)ˣ) :
    sourceArchimedeanScalarActual A (a * b) =
      sourceArchimedeanScalarActual A a * sourceArchimedeanScalarActual A b :=
  map_mul (sourceArchimedeanScalarActual A) a b

end LeanFormal.IUT.XiFPaper.S3139C1InfinitePlaceActual

end
