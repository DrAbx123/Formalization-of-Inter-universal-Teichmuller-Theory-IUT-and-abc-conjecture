import tmp.sheaf.xif.paper.OtriangleLogVolumeObjectActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import LeanFormal.IUT.Foundations.Volumes.HaarLogVolume

/-! # S185: actual nonunit Haar and root-theta normalization objects

Nonunit Haar: the additive Haar on the common-prime completion, restricted to the
O-triangle boundary set sourceOBoundaryMonoid.

Root-theta normalization: the actual paperRootThetaUnit family together with the
completion Haar, plus the exact missing root-theta norm normalization.

No inequality/no fake Haar/root normalization/sorry/axiom/True/PUnit.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S185HaarRootThetaActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.OtriangleLogVolumeObjectActual
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open MeasureTheory

universe u v

variable {l : PrimeGeFive} {V : Type v} [Fintype V]
variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

noncomputable instance commonPrimeCompletionMeasurableSpace
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime K p) :
    MeasurableSpace (CommonPrimeCompletion place) := borel _

noncomputable instance commonPrimeCompletionBorelSpace
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime K p) :
    BorelSpace (CommonPrimeCompletion place) := ⟨rfl⟩

/-- Actual additive Haar on the common-prime completion. -/
noncomputable def completionAddHaar :
    Measure (CommonPrimeCompletion place) := by
  exact Measure.addHaar

/-- Actual nonunit Haar: completion Haar restricted to the O-triangle boundary. -/
noncomputable def nonunitHaarMeasure :
    Measure (CommonPrimeCompletion place) :=
  completionAddHaar place |>.restrict
    (sourceOBoundaryMonoid (K := K) (p := p) place :
      Set (CommonPrimeCompletion place))

/-- Actual nonunit measure object. -/
structure NonunitHaarObject where
  carrierSet : Set (CommonPrimeCompletion place)
  carrierSet_eq : carrierSet =
    (sourceOBoundaryMonoid (K := K) (p := p) place :
      Set (CommonPrimeCompletion place))
  measure : Measure (CommonPrimeCompletion place)
  measure_eq : measure = nonunitHaarMeasure place

/-- Actual nonunit Haar object. -/
noncomputable def nonunitHaarObject :
    NonunitHaarObject (K := K) (p := p) place where
  carrierSet :=
    (sourceOBoundaryMonoid (K := K) (p := p) place :
      Set (CommonPrimeCompletion place))
  carrierSet_eq := rfl
  measure := nonunitHaarMeasure place
  measure_eq := rfl

/-- Exact missing root-theta norm normalization over the root-extension carrier. -/
structure RootThetaNormGapOver (G : CompletionValuedSourceGeometry
    (l := l) (K := K) (p := p) V) where
  rootCarrier : Type (max u v)
  completionHaar : (v : V) → Measure (CommonPrimeCompletion (G.place v))
  normMap : Prop

/-- Actual root-theta normalization object: actual paperRootThetaUnit family plus
completion Haar, with exact missing root-theta norm normalization. -/
structure RootThetaNormalizationObject
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (j : SignedLabel l.value) where
  rootUnit : (v : V) → (RootExtension (G := G) v)ˣ
  rootUnit_eq : rootUnit = fun v => paperRootThetaUnit (G := G) j v
  haar : (v : V) → Measure (CommonPrimeCompletion (G.place v))
  haar_eq : haar = fun v => completionAddHaar (G.place v)
  rootNormGap : Prop

/-- Actual root-theta normalization object. -/
noncomputable def rootThetaNormalizationObject
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (j : SignedLabel l.value) :
    RootThetaNormalizationObject (l := l) (K := K) (p := p) (V := V) G j where
  rootUnit := fun v => paperRootThetaUnit (G := G) j v
  rootUnit_eq := rfl
  haar := fun v => completionAddHaar (G.place v)
  haar_eq := rfl
  rootNormGap :=
    ∀ v, Nonempty (RootThetaNormalizationGap K p (G.place v))

/-- Completed O-triangle log-volume object: formal boundary/quotient base plus the
actual nonunit Haar restriction and actual root-theta normalization object. -/
structure OtriangleLogVolumeCompletedObject
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (j : SignedLabel l.value) where
  base : OtriangleLogVolumeObject (K := K) (p := p) place
  nonunitHaar : NonunitHaarObject (K := K) (p := p) place
  rootTheta : RootThetaNormalizationObject (l := l) (K := K) (p := p) (V := V) G j

/-- Actual completed O-triangle log-volume object. -/
noncomputable def otriangleLogVolumeCompletedObject
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (j : SignedLabel l.value) :
    OtriangleLogVolumeCompletedObject (l := l) (K := K) (p := p)
      (place := place) (V := V) G j where
  base := otriangleLogVolumeObject (K := K) (p := p) place
  nonunitHaar := nonunitHaarObject (K := K) (p := p) place
  rootTheta := rootThetaNormalizationObject (l := l) (K := K) (p := p) (V := V) G j

end LeanFormal.IUT.XiFPaper.S185HaarRootThetaActual

end
