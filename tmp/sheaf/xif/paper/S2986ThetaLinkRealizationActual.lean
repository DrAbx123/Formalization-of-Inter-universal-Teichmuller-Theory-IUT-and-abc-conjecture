import tmp.sheaf.xif.paper.S2920ThetaLinkHeight
import tmp.sheaf.xif.paper.S2921HeightBridgeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2920ThetaLinkHeight
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2986ThetaLinkRealizationActual

/-- Real D/Q/S/T realized from the actual S2921 candidates. -/
structure S2986ThetaLinkRealization where
  D : Real
  Q : Nat -> Nat -> Nat -> Real
  S : Nat -> Nat -> Nat -> Real
  T : Nat -> Nat -> Nat -> Real
  D_eq : D = S2921D
  Q_eq : forall a b c, Q a b c = S2921Q a b c
  S_eq : forall a b c, S a b c = S2921S a b c
  T_eq : forall a b c, T a b c = S2921T a b c

noncomputable def S2986ThetaLinkRealization.ofS2921 :
    S2986ThetaLinkRealization where
  D := S2921D
  Q := S2921Q
  S := S2921S
  T := S2921T
  D_eq := rfl
  Q_eq := fun _ _ _ => rfl
  S_eq := fun _ _ _ => rfl
  T_eq := fun _ _ _ => rfl

/-- The actual theta-link generator law (algebraic degree law). -/
theorem S2986_thetaLink_generator
    {U V G H : Type*} [Group U] [Group V] [CommGroup G] [CommGroup H]
    (u : U →* G) (v : V →* H) (q : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hunitG : ∀ a, degreeG (u a) = 1)
    (hunitH : ∀ b, degreeH (v b) = 1)
    (hq : (degreeG q).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0)
    (e : U ≃* V) :
    thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (distinguishedGenerator u q) = distinguishedGenerator v theta :=
  S2920_thetaLink_generator u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e

/-- The unproved analytic bridge: J-height ≤ procession average for the
realized D/Q/S/T. -/
def S2986HeightLeProcession (R : S2986ThetaLinkRealization)
    (n : Nat) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    Height.logHeight₁ (abcJInvariant a b c) <=
    (1 / (n : Real)) *
      ∑ j ∈ Icc 1 n,
        LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
          (2 * (n : Real) + 1) R.D (R.Q a b c) (R.S a b c) (R.T a b c) j

#check S2986ThetaLinkRealization
#check S2986ThetaLinkRealization.ofS2921
#check S2986_thetaLink_generator
#check S2986HeightLeProcession
#print axioms S2986_thetaLink_generator

end LeanFormal.IUT.XiFPaper.S2986ThetaLinkRealizationActual
end
