import tmp.sheaf.xif.paper.S3139FieldCArchimedeanLogActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: field (C) consumer — actual archimedean Real scalar channel for the lattice/mainline streams

Consumer interface for the field-(C) archimedean realification: the actual
Real scalar character of `F_mod^x` from the production archimedean log at a
supplied infinite place, exposed in the shape the copy action and the
lattice/mainline q/Theta readouts consume (IUT III:616-620, Fig. I.5).

The character is multiplicative (a monoid hom into `R^x`) and is built from the
actual additive norm-log `infinitePlaceLog` of the completion; the archimedean
place itself is the explicit choice datum `SourceInfinitePlaceChoice`.

**Component, not paper object.**  Named consumers: `SourceInd2CopyActionData`
(task-27 shape) and the lattice/mainline R1/M-fields q/Theta comparison.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The archimedean Real scalar channel of the copies at a supplied infinite
place, as a multiplicative character of `F_mod^x`. -/
noncomputable def sourceArchimedeanCopyScalar
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceInfinitePlaceChoice I.initial.arithmetic) :
    (I.initial.arithmetic.Fmod)ˣ →* ℝˣ :=
  sourceInfinitePlaceScalarCharacter I.initial.arithmetic c

/-- The channel is multiplicative: the product of two copies acts by the
product of scalars (the monoid-hom law consumed by the copy action). -/
theorem sourceArchimedeanCopyScalar_mul
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceInfinitePlaceChoice I.initial.arithmetic)
    (a b : (I.initial.arithmetic.Fmod)ˣ) :
    sourceArchimedeanCopyScalar I c (a * b) =
      sourceArchimedeanCopyScalar I c a * sourceArchimedeanCopyScalar I c b :=
  map_mul (sourceArchimedeanCopyScalar I c) a b

/-- The channel sends the unit copy to the unit scalar. -/
theorem sourceArchimedeanCopyScalar_one
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceInfinitePlaceChoice I.initial.arithmetic) :
    sourceArchimedeanCopyScalar I c 1 = 1 :=
  map_one (sourceArchimedeanCopyScalar I c)

/-- The scalar of a unit is a positive real number (the character lands in
`R^x`, i.e. the realified scalar is nonzero). -/
theorem sourceArchimedeanCopyScalar_ne_zero
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceInfinitePlaceChoice I.initial.arithmetic)
    (a : (I.initial.arithmetic.Fmod)ˣ) :
    (sourceArchimedeanCopyScalar I c a : ℝ) ≠ 0 :=
  Units.ne_zero (sourceArchimedeanCopyScalar I c a)

end LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanConsumerActual

end
