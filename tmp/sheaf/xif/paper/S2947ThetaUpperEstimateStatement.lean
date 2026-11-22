import tmp.sheaf.xif.paper.S2714CThetaUpperInventoryActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2947ThetaUpperEstimateStatement

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Exact IUT IV theta upper-estimate target: the source signed theta hull
log-volume is bounded by the printed CTheta times |log q|. -/
def S2947ThetaUpperEstimate
    (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (q : Real)
    (dmod dFpd fFpd eStar etaPrm : Real) : Prop :=
  I.sourceSignedHullLogVolume v R n ≤
    CTheta l (Real.log q) dmod dFpd fFpd eStar etaPrm * |Real.log q|

/-- The theta-link degree data attached to the estimate.  thetaLink is the
actual algebraic equivalence; thetaSigned is the source signed hull volume and
its identification with the link is kept explicit. -/
structure S2947ThetaLinkData
    {U V' G H : Type*} [Group U] [Group V'] [CommGroup G] [CommGroup H]
    (u : U →* G) (v' : V' →* H) (qbar : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v')
    (hunitG : ∀ a, degreeG (u a) = 1)
    (hunitH : ∀ b, degreeH (v' b) = 1)
    (hq : (degreeG qbar).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0) where
  e : U ≃* V'
  link : ↥(unitGeneratedSubmonoid u qbar) ≃* ↥(unitGeneratedSubmonoid v' theta)
  link_eq : link = thetaLink u v' qbar theta degreeG degreeH hu hv
    hunitG hunitH hq htheta e
  thetaSigned : Real
  q : Real
  q_log_ne_zero : Real.log q ≠ 0

/-- Reusable actual: the trivial upper estimate with C = 0, from the actual
nonpositivity of the source signed hull volume. -/
theorem S2947_sourceSignedHull_upper_zero
    (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (q : Real) :
    I.sourceSignedHullLogVolume v R n ≤ (0 : Real) * |Real.log q| :=
  S2714_sourceSignedHull_upper_zero v R n q

/-- Reusable actual: any theta upper estimate plus the xi-f lower inclusion
gives the CTheta lower bound -1. -/
theorem S2947_cThetaLowerBound_of_upper
    {theta q : Real} (hq : Real.log q ≠ 0)
    (hincl : -|Real.log q| ≤ theta) {C : Real}
    (hupper : theta ≤ C * |Real.log q|) :
    -1 ≤ C :=
  S2714_cThetaLowerBound_of_upper hq hincl hupper

/-- The exact printed CTheta formula from S2691 is available as a definition. -/
theorem S2947_CTheta_formula
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real) :
    CTheta l logQ dmod dFpd fFpd eStar etaPrm =
      (((l.value : Real) + 1) / 4 * paperQAbsLog l logQ) *
          cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm - 1 :=
  CTheta_def_eq l logQ dmod dFpd fFpd eStar etaPrm

/-- Reusable actual: theta-link sends the distinguished generator to Theta. -/
theorem S2947_thetaLink_generator
    {U V' G H : Type*} [Group U] [Group V'] [CommGroup G] [CommGroup H]
    (u : U →* G) (v' : V' →* H) (qbar : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v')
    (hunitG : ∀ a, degreeG (u a) = 1)
    (hunitH : ∀ b, degreeH (v' b) = 1)
    (hq : (degreeG qbar).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0)
    (e : U ≃* V') :
    thetaLink u v' qbar theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (distinguishedGenerator u qbar) = distinguishedGenerator v' theta :=
  thetaLink_generator u v' qbar theta degreeG degreeH hu hv hunitG hunitH
    hq htheta e

/-!
## First error / missing object

The exact target S2947ThetaUpperEstimate is a genuine analytic bound on
I.sourceSignedHullLogVolume.  The actual reusable pieces are:

* S2947_sourceSignedHull_upper_zero: only the trivial C = 0 estimate;
* S2947_cThetaLowerBound_of_upper: the arithmetic transfer, conditional on an
  upper estimate;
* S2947_CTheta_formula: the printed CTheta definition from S2691;
* S2947_thetaLink_generator: the algebraic thetaLink generator law.

None of these proves S2947ThetaUpperEstimate with the printed CTheta.  The
missing object is the analytic bound

  sourceSignedHullLogVolume <= CTheta * |log q|,

which is the IUT IV theta upper estimate.  thetaLink is algebraic and has no
sourceSignedHullLogVolume in its type; the trivial C = 0 bound is not the
printed CTheta bound.

No estimate is faked.  This file is statement-level only.
-/

#check S2947ThetaUpperEstimate
#check S2947ThetaLinkData
#check S2947_sourceSignedHull_upper_zero
#check S2947_cThetaLowerBound_of_upper
#check S2947_CTheta_formula
#check S2947_thetaLink_generator

end LeanFormal.IUT.XiFPaper.S2947ThetaUpperEstimateStatement
end
