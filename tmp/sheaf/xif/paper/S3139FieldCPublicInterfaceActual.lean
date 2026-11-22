import tmp.sheaf.xif.paper.S3139FieldCArchimedeanConsumerActual
import tmp.sheaf.xif.paper.S3139FieldCConjugateConsumerActual
import tmp.sheaf.xif.paper.S3139FieldCResidualSummaryActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: field (C) public interface for the lattice/mainline consumers

Aggregate consumer interface of the first-triangle field (C) (the Real scalar
channel of the `F_mod^x` copies, IUT III:616-620, Fig. I.5):

* `sourceArchimedeanCopyScalar` (from `S3139FieldCArchimedeanConsumerActual`):
  the actual multiplicative Real scalar character of `F_mod^x` at a supplied
  infinite place, with its multiplicativity/unit/nonzero laws — this is the
  paper-faithful realified copy scalar to be consumed by the q/Theta readouts
  (no ring embedding needed).
* `sourceConjugateRealReadout` / `sourceConjugateFiberAut` (from
  `S3139FieldCConjugateConsumerActual`): the finite-place conjugate channel
  readouts, available once the exact missing conjugate datum is supplied.
* residual summary and the (Ind1) bridge dependency from
  `S3139FieldCResidualSummaryActual` / `S3139FieldCConjugateActual`.

**Component, not paper object.**  Named consumers: lattice/mainline q/Theta
comparison and R1/M-fields; first-triangle mutation and
`SourceInd2CopyActionData`.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FieldCPublicInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanConsumerActual
open LeanFormal.IUT.XiFPaper.S3139FieldCConjugateConsumerActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The public realified copy scalar of the actual `F_mod^x`: the archimedean
character at a supplied infinite place. -/
noncomputable def publicCopyScalar
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceInfinitePlaceChoice I.initial.arithmetic) :
    (I.initial.arithmetic.Fmod)ˣ →* ℝˣ :=
  sourceArchimedeanCopyScalar I c

/-- The public realified copy scalar is multiplicative (the law consumed by the
copy action and the q/Theta comparison). -/
theorem publicCopyScalar_mul
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceInfinitePlaceChoice I.initial.arithmetic)
    (a b : (I.initial.arithmetic.Fmod)ˣ) :
    publicCopyScalar I c (a * b) =
      publicCopyScalar I c a * publicCopyScalar I c b :=
  sourceArchimedeanCopyScalar_mul I c a b

/-- The public realified copy scalar of the unit copy is the unit scalar. -/
theorem publicCopyScalar_one
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceInfinitePlaceChoice I.initial.arithmetic) :
    publicCopyScalar I c 1 = 1 :=
  sourceArchimedeanCopyScalar_one I c

end LeanFormal.IUT.XiFPaper.S3139FieldCPublicInterfaceActual

end
