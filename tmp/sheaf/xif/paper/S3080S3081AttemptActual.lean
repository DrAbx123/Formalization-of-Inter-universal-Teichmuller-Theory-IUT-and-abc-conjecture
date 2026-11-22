import tmp.sheaf.xif.paper.S3079GlobalSumIdentificationAttempt
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullSumActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3079GlobalSumIdentificationAttempt
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3080S3081AttemptActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- S3080 target: an equivalence from the source place type V to the native
bad family. -/
def S3080IndexEquivalence : Prop :=
  Nonempty (V ≃ Bad (nativePlaceSelection T))

/-- Conditional construction of S3080 from a V/badPlaces equivalence and the
known badPlaces/nativeBad bridge. -/
theorem S3080_of_badPlaces_equiv
    (f : V ≃ I.initial.badPlaces)
    (g : I.initial.badPlaces ≃ Bad (nativePlaceSelection T)) :
    S3080IndexEquivalence (l := l) (V := V) T :=
  ⟨f.trans g⟩

/-- Exact S3081 per-place target, parameterized by the S3080 equivalence. -/
def S3081PerPlaceHullLocalFormula
    (I : OriginalInput l V)
    (R : forall v : V, I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (T : SourceNativeInitialThetaData.{0} l)
    (e : V ≃ Bad (nativePlaceSelection T)) : Prop :=
  forall v : V,
    Real.log (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal =
      GlobalQVFamThetaHullSumActual.localThetaHullLogFormula T (e.toFun v)

/-- Conditional S3081 from a per-place equality hypothesis. -/
theorem S3081_of_perPlace (e : V ≃ Bad (nativePlaceSelection T))
    (h : S3081PerPlaceHullLocalFormula (l := l) I R n T e) :
    S3081PerPlaceHullLocalFormula (l := l) (I := I) (R := R) (n := n) (T := T) e := h

#check S3080IndexEquivalence
#check S3080_of_badPlaces_equiv
#check S3081PerPlaceHullLocalFormula

end LeanFormal.IUT.XiFPaper.S3080S3081AttemptActual
end