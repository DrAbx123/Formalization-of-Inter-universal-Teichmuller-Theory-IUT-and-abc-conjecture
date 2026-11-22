import tmp.sheaf.xif.paper.S3139FieldCArchimedeanLogActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: field (C) — archimedean realification bundle (choice + actual character)

Bundle of the field-(C) archimedean realification data: the explicit choice of
an infinite place of the actual `F_mod` together with the actual Real scalar
character of `F_mod^x` computed from the production archimedean additive log,
with its multiplicativity laws.  This is the paper-faithful realified scalar
channel exposed for the copy action and for the lattice/mainline q/Theta
readouts (IUT III:616-620, Fig. I.5).

**Component, not paper object.**  Named consumers: `SourceInd2CopyActionData`
and the lattice/mainline q/Theta comparison.  No sorry/axiom/True/PUnit/toy.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The archimedean realification bundle: a chosen infinite place of the
actual `F_mod` and the actual Real scalar character of `F_mod^x` it induces. -/
structure SourceArchimedeanRealification
    (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l) where
  /-- the chosen infinite place of the actual F_mod -/
  place : SourceInfinitePlaceChoice A
  /-- the actual Real scalar character of the copies -/
  scalar : (A.Fmod)ˣ →* ℝˣ
  /-- the scalar is the actual archimedean character at the chosen place -/
  scalar_eq : scalar = sourceFmodArchimedeanScalarCharacter A place

/-- The canonical realification bundle for any supplied infinite-place
choice. -/
noncomputable def SourceArchimedeanRealification.ofChoice
    (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l)
    (c : SourceInfinitePlaceChoice A) :
    SourceArchimedeanRealification A where
  place := c
  scalar := sourceFmodArchimedeanScalarCharacter A c
  scalar_eq := rfl

/-- The bundled character is multiplicative. -/
theorem SourceArchimedeanRealification.scalar_mul
    {A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l}
    (R : SourceArchimedeanRealification A) (a b : (A.Fmod)ˣ) :
    R.scalar (a * b) = R.scalar a * R.scalar b :=
  map_mul R.scalar a b

/-- The bundled character of the unit copy is the unit scalar. -/
theorem SourceArchimedeanRealification.scalar_one
    {A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l}
    (R : SourceArchimedeanRealification A) :
    R.scalar 1 = 1 :=
  map_one R.scalar

end LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanBundleActual

end
