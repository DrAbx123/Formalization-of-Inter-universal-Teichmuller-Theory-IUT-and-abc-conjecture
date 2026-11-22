import tmp.sheaf.xif.paper.S2974VerticalCoricityGateActual
import tmp.sheaf.xif.paper.S2953CThetaFromCertificateActual
import LeanFormal.IUT.IUTIII.Corollary312.TateQPilotJComparison
import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2974VerticalCoricityGateActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2975ThetaLinkCoricityConnection

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Actual q-pilot coricity gate reused from S2974. -/
noncomputable abbrev S2975Gate : I.VerticalCoricityGate :=
  S2974VerticalCoricityGate I

/-- Actual induced DTheta realization gate. -/
noncomputable abbrev S2975Realization : I.DThetaRealizationGate :=
  S2974DThetaRealizationGate I

/-- Actual q-pilot log-volume from the Tate q-pilot. -/
noncomputable def S2975Q (l : PrimeGeFive) [Fact (Nat.Prime l.value)] : Real :=
  LeanFormal.IUT.TateCurvePadic.qPilotLogVolume l

theorem S2975Q_eq_log (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    S2975Q l = Real.log (l.value : Real) :=
  LeanFormal.IUT.TateCurvePadic.qPilotLogVolume_eq_log_prime l

/-- The exact theta upper target for the coricity-thetaLink connection. -/
def S2975ThetaUpperTarget
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)]
    (thetaSigned logQ dmod dFpd fFpd eStar etaPrm : Real) : Prop :=
  thetaSigned ≤
    CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * S2975Q l

/-- Actual pairing of the coricity gate with a thetaLink equivalence.  The
connection is a structure: it records both the D-side gate and the algebraic
thetaLink, with the identification of the link as an explicit field. -/
structure S2975CoricityThetaLink
    {U V' G H : Type*} [Group U] [Group V'] [CommGroup G] [CommGroup H]
    (u : U →* G) (v' : V' →* H) (qbar : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v')
    (hunitG : ∀ a, degreeG (u a) = 1)
    (hunitH : ∀ b, degreeH (v' b) = 1)
    (hq : (degreeG qbar).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0) where
  gate : I.VerticalCoricityGate
  realization : I.DThetaRealizationGate
  e : U ≃* V'
  link : ↥(unitGeneratedSubmonoid u qbar) ≃* ↥(unitGeneratedSubmonoid v' theta)
  link_eq : link = thetaLink u v' qbar theta degreeG degreeH hu hv
    hunitG hunitH hq htheta e

/-- Actual connection from the S2974 gate and an explicit thetaLink. -/
noncomputable def S2975Connection
    {U V' G H : Type*} [Group U] [Group V'] [CommGroup G] [CommGroup H]
    (u : U →* G) (v' : V' →* H) (qbar : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v')
    (hunitG : ∀ a, degreeG (u a) = 1)
    (hunitH : ∀ b, degreeH (v' b) = 1)
    (hq : (degreeG qbar).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0)
    (e : U ≃* V') : S2975CoricityThetaLink (I := I)
      u v' qbar theta degreeG degreeH hu hv hunitG hunitH hq htheta where
  gate := S2975Gate (I := I)
  realization := S2975Realization (I := I)
  e := e
  link := thetaLink u v' qbar theta degreeG degreeH hu hv hunitG hunitH
    hq htheta e
  link_eq := rfl

/-- Actual thetaLink generator law inside a connection. -/
theorem S2975_connection_generator
    {U V' G H : Type*} [Group U] [Group V'] [CommGroup G] [CommGroup H]
    (u : U →* G) (v' : V' →* H) (qbar : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v')
    (hunitG : ∀ a, degreeG (u a) = 1)
    (hunitH : ∀ b, degreeH (v' b) = 1)
    (hq : (degreeG qbar).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0)
    (e : U ≃* V')
    (C : S2975CoricityThetaLink (I := I)
      u v' qbar theta degreeG degreeH hu hv hunitG hunitH hq htheta) :
    C.link (distinguishedGenerator u qbar) = distinguishedGenerator v' theta := by
  rw [C.link_eq]
  exact thetaLink_generator u v' qbar theta degreeG degreeH hu hv hunitG hunitH
    hq htheta C.e

/-- Consumer: exact theta upper target gives the CThetaPaper lower bound. -/
theorem S2975_to_CThetaPaper_lowerBound
    {label : Type} [Fintype label]
    (C : S2953CThetaUpperCertificate label l)
    (hq : Real.log C.q ≠ 0)
    (htarget : C.thetaLogVolume ≤
      CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm *
        |Real.log C.q|) :
    -1 ≤ CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm :=
  S2953_CThetaPaper_lower_bound l C hq

/-!
## First error / missing object

The actual connection is S2975Connection: it pairs the actual S2974 coricity
gate with an explicit ThetaLinkAssembly.thetaLink equivalence and records the
link identification.  The actual thetaLink generator law is
S2975_connection_generator.

What is missing: any theorem relating the S2974 gate / D-theater data to the
real thetaSigned (sourceSignedHullLogVolume) or to the CThetaPaper bound.
S2975ThetaUpperTarget is only a proposition; no analytic bridge from the
D-prime-strip gate to thetaSigned exists in the tree.

The gate fields are D-prime-strip data (dTheater, verticalLink, bridge).
thetaLink is an algebraic equivalence of unit-generated submonoids.  Neither
contains Height.logHeight, sourceSignedHullLogVolume, CThetaPaper, or a real
upper estimate.  Thus the theta upper target cannot be proved from the gate and
thetaLink alone; the exact missing object is the analytic/coricity comparison
gate-to-thetaSigned.  No ABC input and no fake estimate is used.
-/

#check S2975Gate
#check S2975Realization
#check S2975Q
#check S2975Q_eq_log
#check S2975ThetaUpperTarget
#check S2975CoricityThetaLink
#check S2975Connection
#check S2975_connection_generator
#check S2975_to_CThetaPaper_lowerBound
#print axioms S2975_connection_generator

end LeanFormal.IUT.XiFPaper.S2975ThetaLinkCoricityConnection
end
