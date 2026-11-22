import tmp.sheaf.xif.paper.S2268LocalBridgeActual
import tmp.sheaf.xif.paper.S2232Layer1PrimeAlignmentActual
import tmp.sheaf.xif.paper.S2135Layer1SplitActual

/-! # S2280: paper V-prime matching from the known strip-alignment input

S2280 reduces `S2268PaperVPrimeMatchRequired` to the already isolated exact
missing input `S2135PrimeAlignmentRequired` (`qVFamTensorP T b ∈ primeStrip 2 7`).
The rational prime of `sectionKPlace T b` is proved equal to `qVFamTensorP T b`, so
strip membership constructs the paper place v and closes the S2264 bridge. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2280PaperVPrimeMatchActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2268LocalBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2232Layer1PrimeAlignmentActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2034OperationKummerActual
open LeanFormal.IUT.XiFPaper.S2264StripQuotientIdActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem s2280_sectionKPlace_prime_eq_qVFamTensorP :
    s2268p T b = qVFamTensorP T b := by
  rw [s2268p, s2232_completionRationalPrime_val_eq_residueCharacteristic]
  rw [← residueCharacteristic_comap (k := T.arithmetic.F)
    (K := T.arithmetic.K) (sectionKPlace T b)]
  rw [sectionKPlace_comap]
  rw [← residueCharacteristic_comap (k := T.arithmetic.Fmod)
    (K := T.arithmetic.F) (sectionFPlace T b)]
  rw [sectionFPlace_comap]
  rw [← s2232_qVFamTensorP_eq_b_residueCharacteristic T b]

/-- The exact missing strip-alignment input is exactly S2135. -/
abbrev S2280QVFamPrimeStripRequired : Prop :=
  S2135PrimeAlignmentRequired T b

/-- Strip alignment constructs the paper V-prime matching S2268. -/
theorem s2280PaperVPrimeMatch_of_strip
    (h : S2135PrimeAlignmentRequired T b) :
    S2268PaperVPrimeMatchRequired T b :=
  ⟨⟨qVFamTensorP T b, h⟩, (s2280_sectionKPlace_prime_eq_qVFamTensorP T b).symm⟩

/-- Strip alignment closes the S2264 local bridge explicitly. -/
noncomputable def s2280S2264BridgeOfStrip
    (h : S2135PrimeAlignmentRequired T b) :
    S2264ActualLocalBridgeRequired T b :=
  s2268S2264BridgeOfPlace T b ⟨qVFamTensorP T b, h⟩
    (s2280_sectionKPlace_prime_eq_qVFamTensorP T b).symm

#check s2280_sectionKPlace_prime_eq_qVFamTensorP
#check S2280QVFamPrimeStripRequired
#check s2280PaperVPrimeMatch_of_strip
#check s2280S2264BridgeOfStrip

end LeanFormal.IUT.XiFPaper.S2280PaperVPrimeMatchActual
end
