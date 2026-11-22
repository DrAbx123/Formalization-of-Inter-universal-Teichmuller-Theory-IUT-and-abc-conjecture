import tmp.sheaf.xif.paper.S2714CThetaUpperInventoryActual
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import LeanFormal.IUT.IUTIII.Corollary312.TateQPilotJComparison
import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2951ThetaSignedActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
local instance : Fact (Nat.Prime l.value) := ⟨l.prime⟩

/-- Actual thetaSigned: the source signed hull log-volume. -/
noncomputable def S2951ThetaSigned
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) : Real :=
  I.sourceSignedHullLogVolume v R n

/-- Actual qParameter: the norm of the canonical Tate q-pilot. -/
noncomputable def S2951QParameter (l : PrimeGeFive) [Fact (Nat.Prime l.value)] : Real :=
  ‖LeanFormal.IUT.TateCurvePadic.q l‖

/-- The exact theta upper target with the paper-scale CTheta. -/
def S2951ThetaUpperTarget
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (dmod dFpd fFpd eStar etaPrm : Real) : Prop :=
  S2951ThetaSigned v R n ≤
    CThetaPaper l (Real.log (S2951QParameter l)) dmod dFpd fFpd eStar etaPrm *
      |Real.log (S2951QParameter l)|

/-- Actual: thetaSigned is nonpositive. -/
theorem S2951_thetaSigned_nonpos
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    S2951ThetaSigned v R n ≤ 0 := by
  unfold S2951ThetaSigned
  exact I.sourceSignedHullLogVolume_nonpos v R n

/-- Actual trivial C = 0 upper estimate. -/
theorem S2951_thetaUpper_zero
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) (q : Real) :
    S2951ThetaSigned v R n ≤ (0 : Real) * |Real.log q| := by
  rw [zero_mul]
  exact S2951_thetaSigned_nonpos v R n

/-- Consumer: an actual theta upper target plus the xi-f lower inclusion gives
-1 <= CThetaPaper. -/
theorem S2951_to_S2715_lowerBound
    {theta q : Real}
    (hq : Real.log q ≠ 0)
    (hincl : -|Real.log q| ≤ theta)
    {C : Real}
    (hupper : theta ≤ C * |Real.log q|) :
    -1 ≤ C :=
  cor312CThetaLowerBound hq hincl hupper

/-- Reusable actual thetaLink generator law. -/
theorem S2951_thetaLink_generator
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

S2951ThetaUpperTarget is the exact IUT IV theta estimate

  thetaSigned <= CThetaPaper * |log qParameter|.

Actual pieces:
* S2951ThetaSigned is I.sourceSignedHullLogVolume;
* S2951QParameter is the norm of the canonical Tate q-pilot;
* S2951_thetaSigned_nonpos and S2951_thetaUpper_zero give only C = 0;
* S2951_to_S2715_lowerBound is the actual xi-f consumer;
* thetaLink generator law is algebraic.

Missing: the nontrivial upper estimate with CThetaPaper on the right.  The
trivial zero estimate is not enough; no theorem in the tree relates
sourceSignedHullLogVolume to CThetaPaper except the conditional consumer.
No estimate is faked.
-/

#check S2951ThetaSigned
#check S2951QParameter
#check S2951ThetaUpperTarget
#check S2951_thetaSigned_nonpos
#check S2951_thetaUpper_zero
#check S2951_to_S2715_lowerBound
#check S2951_thetaLink_generator
#print axioms S2951_thetaSigned_nonpos
#print axioms S2951_to_S2715_lowerBound

end LeanFormal.IUT.XiFPaper.S2951ThetaSignedActual
end
