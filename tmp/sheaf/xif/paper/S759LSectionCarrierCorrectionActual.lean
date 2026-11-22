import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import Mathlib.Algebra.Group.TypeTags.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S759LSectionCarrierCorrectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Finite L carrier: L units times an explicit real divisor coordinate. -/
abbrev LSectionCarrier : Type :=
  (rootNormedExtension T b)ˣ × Multiplicative Real

/-- Divisor coordinate. -/
noncomputable def lDivisorSection (u : LSectionCarrier T b) : Multiplicative Real := u.2

/-- q section in L: root^(2l). -/
noncomputable def lQSection : LSectionCarrier T b :=
  (rootNormedUnit T b ^ (2 * l.value), Multiplicative.ofAdd ((qVFamily T b).order : Real))

/-- root section in L: the actual 2l-th root. -/
noncomputable def lRootSection : LSectionCarrier T b :=
  (rootNormedUnit T b, Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)))

theorem lRootSection_pow : lRootSection T b ^ (2 * l.value) = lQSection T b := by
  apply Prod.ext
  · rfl
  · change Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)) ^
        (2 * l.value) = Multiplicative.ofAdd ((qVFamily T b).order : Real)
    rw [← ofAdd_nsmul, nsmul_eq_mul]
    congr 1
    have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
    field_simp [hl]
    push_cast
    ring

/-- Inclusion of L units into the ambient algebraic closure units. -/
noncomputable def lUnitInclusion : (rootNormedExtension T b)ˣ →*
    (AlgebraicClosure (sourceRootField T b))ˣ :=
  Units.map (rootNormedExtension T b).subtype.toMonoidHom

end LeanFormal.IUT.XiFPaper.S759LSectionCarrierCorrectionActual

end
