import tmp.sheaf.xif.paper.S150SourceLogVolumeNormalizationActual
import tmp.sheaf.xif.paper.S104CanonicalLogPiActual

/-! # S170: actual O-triangle log-volume object

This object bundles, without proving any inequality:

* the O-triangle carrier (sourceOBoundaryMonoid);
* the actual integral log-shell set and its O-times unit logarithm;
* the formal boundary log in K x Z with symbolic canonical logPi = (0,1);
* the quotient normalized log in K / unitLogRange;
* the object-level gaps: actual canonical log(pi), nonunit Haar, and root-theta
  normalization.

No inequality/no fake field log/Haar/root-theta/sorry/axiom/True/PUnit.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.OtriangleLogVolumeObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual
open LeanFormal.IUT.XiFPaper.S104CanonicalLogPiActual
open LeanFormal.IUT.XiFPaper.S111FormalBoundaryLogActual
open LeanFormal.IUT.XiFPaper.S143dQuotientLogVolumeActual
open LeanFormal.IUT.XiFPaper.S150SourceLogVolumeNormalizationActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Exact missing nonunit Haar data on the O-triangle boundary. -/
structure NonunitHaarGap (K : Type u) [Field K] [NumberField K]
    (p : Nat) [Fact p.Prime] (place : FinitePlaceAtPrime K p) where
  carrier : Type u
  measure : carrier → Real
  measure_eq : Prop

/-- Exact missing nonunit Haar requirement; no inhabitant asserted. -/
def NonunitHaarRequired : Prop :=
  Nonempty (NonunitHaarGap K p place)

/-- Exact missing root-theta normalization data. -/
structure RootThetaNormalizationGap (K : Type u) [Field K] [NumberField K]
    (p : Nat) [Fact p.Prime] (place : FinitePlaceAtPrime K p) where
  qParameterValue : Real
  rootCarrier : Type u
  normMap : Prop

/-- Exact missing root-theta normalization; no inhabitant asserted. -/
def RootThetaNormalizationRequired : Prop :=
  Nonempty (RootThetaNormalizationGap K p place)

/-- Actual O-triangle log-volume object. -/
structure OtriangleLogVolumeObject where
  integralLogShell : Set (CommonPrimeCompletion place)
  integralLogShell_eq : integralLogShell =
    (LeanFormal.IUT.LocalFieldLogarithm.integralLogShell
      (K := CommonPrimeCompletion place) (p := p) :
      Set (CommonPrimeCompletion place))
  unitLog : (Integers (CommonPrimeCompletion place))ˣ →
    CommonPrimeCompletion place
  unitLog_eq : unitLog =
    LeanFormal.IUT.LocalFieldLogarithm.unitLog (K := CommonPrimeCompletion place)
  formalBoundaryLog : sourceOBoundaryMonoid (K := K) (p := p) place →
    CommonPrimeCompletion place × ℤ
  formalBoundaryLog_eq : formalBoundaryLog = boundaryLogFormal (K := K) (p := p) place
  quotientNormalizedLog : sourceOBoundaryMonoid (K := K) (p := p) place →
    (CommonPrimeCompletion place) ⧸ unitLogRange (K := K) (p := p) place
  quotientNormalizedLog_eq : quotientNormalizedLog =
    normalizedLogVolumeQuot (K := K) (p := p) place
      (dvrUniformizer (K := K) (p := p) place)
      (dvrUniformizer_irreducible (K := K) (p := p) place)
  normalizationScale : CommonPrimeCompletion place
  normalizationScale_eq : normalizationScale = sourceLogVolumeScale place
  normalizedUnitLogMap : (Integers (CommonPrimeCompletion place))ˣ →
    CommonPrimeCompletion place
  normalizedUnitLogMap_eq : normalizedUnitLogMap =
    fun u => (sourceLogVolumeScale place)⁻¹ *
      LeanFormal.IUT.LocalFieldLogarithm.unitLog
        (K := CommonPrimeCompletion place) u
  canonicalLogPiSymbol : CommonPrimeCompletion place × ℤ
  canonicalLogPiSymbol_eq : canonicalLogPiSymbol = (0, 1)
  gap_canonicalLogPi : Prop
  gap_canonicalLogPi_eq : gap_canonicalLogPi =
    CanonicalLogPiRequired place (dvrUniformizer (K := K) (p := p) place)
  gap_nonunitHaar : Prop
  gap_nonunitHaar_eq : gap_nonunitHaar = NonunitHaarRequired place
  gap_rootTheta : Prop
  gap_rootTheta_eq : gap_rootTheta = RootThetaNormalizationRequired place

/-- Actual O-triangle log-volume object, with formal symbolic logPi. -/
noncomputable def otriangleLogVolumeObject :
    OtriangleLogVolumeObject place where
  integralLogShell :=
    (LeanFormal.IUT.LocalFieldLogarithm.integralLogShell
      (K := CommonPrimeCompletion place) (p := p) :
      Set (CommonPrimeCompletion place))
  integralLogShell_eq := rfl
  unitLog := LeanFormal.IUT.LocalFieldLogarithm.unitLog
    (K := CommonPrimeCompletion place)
  unitLog_eq := rfl
  formalBoundaryLog := boundaryLogFormal (K := K) (p := p) place
  formalBoundaryLog_eq := rfl
  quotientNormalizedLog :=
    normalizedLogVolumeQuot (K := K) (p := p) place
      (dvrUniformizer (K := K) (p := p) place)
      (dvrUniformizer_irreducible (K := K) (p := p) place)
  quotientNormalizedLog_eq := rfl
  normalizationScale := sourceLogVolumeScale place
  normalizationScale_eq := rfl
  normalizedUnitLogMap := fun u =>
    (sourceLogVolumeScale place)⁻¹ *
      LeanFormal.IUT.LocalFieldLogarithm.unitLog
        (K := CommonPrimeCompletion place) u
  normalizedUnitLogMap_eq := rfl
  canonicalLogPiSymbol := (0, 1)
  canonicalLogPiSymbol_eq := rfl
  gap_canonicalLogPi :=
    CanonicalLogPiRequired place (dvrUniformizer (K := K) (p := p) place)
  gap_canonicalLogPi_eq := rfl
  gap_nonunitHaar := NonunitHaarRequired place
  gap_nonunitHaar_eq := rfl
  gap_rootTheta := RootThetaNormalizationRequired place
  gap_rootTheta_eq := rfl

/-- The formal canonical log(pi) is the symbolic generator (0,1), not a field
element. -/
theorem otriangleLogVolumeObject_canonicalLogPi :
    (otriangleLogVolumeObject place).canonicalLogPiSymbol =
      (0, 1) := rfl

end LeanFormal.IUT.XiFPaper.OtriangleLogVolumeObjectActual

end
