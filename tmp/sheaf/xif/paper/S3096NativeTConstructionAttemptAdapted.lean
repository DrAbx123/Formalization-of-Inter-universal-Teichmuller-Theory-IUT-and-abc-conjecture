import tmp.sheaf.xif.paper.S2757SourceCompletionNativeActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2757SourceCompletionNativeActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3096NativeTConstructionAttemptAdapted

/-- The selected-place record with V_mod_bad = {5,2161}. -/
abbrev S3096P : SourcePlaceSelection (S2753A) :=
  S2696SelectionTwo fiveLabel

/-- The native T built from the S2757 completion with bad moduli S2696Vbad. -/
noncomputable def S3096NativeT
    (G : SourceSignQuotientGeometricCore S2753A)
    (assembly : SourceClauseAssembly.{0} S2753A (G.toSourceSignQuotientData S3096P)) :
    SourceNativeInitialThetaData fiveLabel :=
  S2757NativeT S2753A G S3096P assembly

/-- The constructed T's native bad moduli set is exactly the S2696 bad set. -/
theorem S3096NativeT_V_mod_bad
    (G : SourceSignQuotientGeometricCore S2753A)
    (assembly : SourceClauseAssembly.{0} S2753A (G.toSourceSignQuotientData S3096P)) :
    (nativePlaceSelection (S3096NativeT G assembly)).V_mod_bad =
      S3096P.V_mod_bad := rfl

/-- The native bad index is literally the source S2696 bad index. -/
noncomputable def S3096NativeBadEquiv
    (G : SourceSignQuotientGeometricCore S2753A)
    [Fintype (Bad (nativePlaceSelection (S3096NativeT G assembly)))]
    (assembly : SourceClauseAssembly.{0} S2753A (G.toSourceSignQuotientData S3096P)) :
    Bad (nativePlaceSelection (S3096NativeT G assembly)) ≃ Bad S3096P :=
  Equiv.refl _

#check S3096NativeT
#check S3096NativeT_V_mod_bad
#check S3096NativeBadEquiv

end LeanFormal.IUT.XiFPaper.S3096NativeTConstructionAttemptAdapted
end