import tmp.sheaf.xif.paper.S3080S3081AttemptActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3080S3081AttemptActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3082S3083AttemptActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- S3082 target: source places V are the abstract badPlaces type. -/
def S3082BadPlacesEquiv : Prop :=
  Nonempty (V ≃ I.initial.badPlaces)

/-- Conditional S3082 from a V/selectedPlaces equivalence followed by a
selectedPlaces/badPlaces equivalence. -/
theorem S3082_of_selectedPlaces
    (f : V ≃ I.initial.selectedPlaces)
    (g : I.initial.selectedPlaces ≃ I.initial.badPlaces) :
    S3082BadPlacesEquiv (l := l) (V := V) (I := I) :=
  ⟨f.trans g⟩

/-- S3083 per-place target, parameterized by the index equivalence. -/
def S3083PerPlaceHullFormula
    (I : OriginalInput l V)
    (R : forall v : V, I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (T : SourceNativeInitialThetaData.{0} l)
    (e : V ≃ Bad (nativePlaceSelection T)) : Prop :=
  forall v : V,
    Real.log (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal =
      GlobalQVFamThetaHullSumActual.localThetaHullLogFormula T (e.toFun v)

#check S3082BadPlacesEquiv
#check S3082_of_selectedPlaces
#check S3083PerPlaceHullFormula

end LeanFormal.IUT.XiFPaper.S3082S3083AttemptActual
end