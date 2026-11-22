import tmp.sheaf.xif.paper.S3096IndexBridgeAttemptActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3096IndexBridgeAttemptActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3099BadFamilyProjectionAttempt

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (P : SourcePlaceSelection T.arithmetic)
variable [Fintype (Bad P)]

/-- Projection from the native bad family to the source rational bad places,
using the native F-place comap and the identification of bad moduli sets. -/
noncomputable def S3099Projection
    (hbad : T.tuple.source.V_mod_bad = P.V_mod_bad) :
    Bad (nativePlaceSelection T) → Bad P :=
  fun b =>
    ⟨b.1, by
      have hb : b.1 ∈ T.tuple.source.V_mod_bad := b.2
      rw [hbad] at hb
      exact hb⟩

/-- The fiber over a source bad place. -/
noncomputable def S3099Fiber
    (hbad : T.tuple.source.V_mod_bad = P.V_mod_bad)
    (p : Bad P) : Type :=
  {b : Bad (nativePlaceSelection T) //
    S3099Projection T P hbad b = p}

/-- Global fiberwise decomposition of the native bad-place sum. -/
theorem S3099_sum_fiberwise
    (hbad : T.tuple.source.V_mod_bad = P.V_mod_bad)
    (g : Bad (nativePlaceSelection T) → Real) :
    (∑ b : Bad (nativePlaceSelection T), g b) =
      ∑ p : Bad P,
        ∑ b in (Finset.univ.filter
          (fun b : Bad (nativePlaceSelection T) =>
            S3099Projection T P hbad b = p)), g b := by
  classical
  symm
  exact Finset.sum_fiberwise Finset.univ
    (fun b : Bad (nativePlaceSelection T) => S3099Projection T P hbad b) g

#check S3099Projection
#check S3099Fiber
#check S3099_sum_fiberwise

end LeanFormal.IUT.XiFPaper.S3099BadFamilyProjectionAttempt
end