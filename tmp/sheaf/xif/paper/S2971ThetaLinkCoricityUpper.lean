import LeanFormal.IUT.IUTIII.Theorem311.SourceDThetaConstruction
import LeanFormal.IUT.IUTIII.Corollary312.TateQPilotJComparison
import tmp.sheaf.xif.paper.S2951ThetaSignedActual
import tmp.sheaf.xif.paper.S2953CThetaFromCertificateActual
import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2951ThetaSignedActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2971ThetaLinkCoricityUpper

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
local instance : Fact (Nat.Prime l.value) := ⟨l.prime⟩

/-- Actual q-pilot coricity gate: the shadow self-gate supplies the source
D-prime-strip family, vertical links and bridge. -/
noncomputable def S2971VerticalCoricityGate : I.VerticalCoricityGate where
  dTheater := (I.dThetaShadow).dStrip
  verticalLink := fun i j => (I.dThetaShadow).dLink i j
  bridge := fun i => DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i)
  source_dTheater := fun i => rfl
  link_source := fun i j => rfl

/-- The induced DThetaRealizationGate. -/
noncomputable def S2971DThetaRealizationGate : I.DThetaRealizationGate :=
  verticalCoricityGate_of_shadow I S2971VerticalCoricityGate

/-- Actual qParameter from the canonical Tate q-pilot norm. -/
noncomputable def S2971QParameter (l : PrimeGeFive) [Fact (Nat.Prime l.value)] : Real :=
  ‖LeanFormal.IUT.TateCurvePadic.q l‖

/-- Actual value of |log qParameter|: it is log(l). -/
theorem S2971_abs_log_qParameter
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    |Real.log (S2971QParameter l)| = Real.log (l.value : Real) := by
  unfold S2971QParameter
  rw [LeanFormal.IUT.TateCurvePadic.q_norm_eq]
  have hl : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
  rw [Real.log_inv]
  rw [abs_neg]
  exact abs_of_pos (Real.log_pos (by exact_mod_cast l.prime.one_lt))

/-- Exact theta upper target with the paper CTheta. -/
def S2971ThetaUpperTarget
    (thetaSigned : Real) (logQ dmod dFpd fFpd eStar etaPrm : Real) : Prop :=
  thetaSigned ≤ CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * |Real.log (S2971QParameter l)|

/-- Consumer: the theta upper target yields the CThetaPaper lower bound. -/
theorem S2971_to_S2715_lowerBound
    {theta : Real} (hq : Real.log (S2971QParameter l) ≠ 0)
    (hincl : -|Real.log (S2971QParameter l)| ≤ theta)
    {C : Real}
    (hupper : theta ≤ C * |Real.log (S2971QParameter l)|) :
    -1 ≤ C :=
  cor312CThetaLowerBound hq hincl hupper

/-- Reusable actual: thetaLink generator law. -/
theorem S2971_thetaLink_generator
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

Actual pieces:
* S2971VerticalCoricityGate: q-pilot coricity gate built from the actual
  dThetaShadow dStrip/dLInk; no field is invented.
* S2971DThetaRealizationGate: the induced realization gate.
* S2971QParameter = ||q l||, with S2971_abs_log_qParameter proving
  |log qParameter| = log(l).
* S2971_to_S2715_lowerBound: the actual CTheta consumer.
* S2971_thetaLink_generator: thetaLink degree law.

Missing: a theorem relating the source D-shadow/coricity data to
S2951ThetaSigned or to the CThetaPaper upper estimate.  The gate has only
D-prime strip data and equivalences; no real theta bound.  The theta upper
target remains a statement, not a theorem.  No estimate is faked.
-/

#check S2971VerticalCoricityGate
#check S2971DThetaRealizationGate
#check S2971QParameter
#check S2971_abs_log_qParameter
#check S2971ThetaUpperTarget
#check S2971_to_S2715_lowerBound
#check S2971_thetaLink_generator
#print axioms S2971_abs_log_qParameter

end LeanFormal.IUT.XiFPaper.S2971ThetaLinkCoricityUpper
end
