import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
import tmp.sheaf.xif.paper.S2919ThetaUpperFromProcession
import tmp.sheaf.xif.paper.S2838HeightComparisonReductionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
open LeanFormal.IUT.XiFPaper.S2919ThetaUpperFromProcession
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2920ThetaLinkHeight

/-- Exact target statement: on every ABC triple, the J-invariant height is at
most the procession average of the label bounds. -/
def S2920HeightLeProcession
    (n : ℕ) (D Q S T : ℝ) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcJInvariant a b c) ≤
      (1 / (n : ℝ)) *
        ∑ j ∈ Icc 1 n,
          LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
            (2 * (n : ℝ) + 1) D Q S T j

/-- Reusable actual: the theta-link sends the distinguished generator q to
Theta. -/
theorem S2920_thetaLink_generator
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
  thetaLink_generator u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e

/-- Reusable actual: the theta-link on unit powers is the corresponding target
unit power. -/
theorem S2920_thetaLink_unitPower
    {U V G H : Type*} [Group U] [Group V] [CommGroup G] [CommGroup H]
    (u : U →* G) (v : V →* H) (q : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hunitG : ∀ a, degreeG (u a) = 1)
    (hunitH : ∀ b, degreeH (v b) = 1)
    (hq : (degreeG q).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0)
    (e : U ≃* V) (a : U) (n : ℕ) :
    thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (unitPowerElement u q a n) = unitPowerElement v theta (e a) n :=
  thetaLink_unitPower u v q theta degreeG degreeH hu hv hunitG hunitH
    hq htheta e a n

/-!
## First missing object

ThetaLinkAssembly.thetaLink has type

  unitGeneratedSubmonoid u q ≃* unitGeneratedSubmonoid v theta

It is a multiplicative equivalence of unit-generated submonoids of two ambient
commutative groups.  Its type contains no height, no ABC triple, no
Height.logHeight₁, no S2792RegionVolume, and no procession average.

S2919.processionAverage_le is a real-number inequality about
collectionBound; its arguments are arbitrary reals D/Q/S/T.

Therefore thetaLink alone cannot imply S2920HeightLeProcession.  The exact
missing bridge is an analytic/geometric identification:

  for every ABC triple, identify the relevant J-invariant height with the
  degree/order data (D,Q,S,T) attached to the source and target theta-link
  monoid elements, and show that the theta-link's exponent/unit comparison
  yields the real inequality

    logHeight₁ (abcJInvariant a b c) <= procession average.

No such bridge is present in the tree: thetaLink is algebraic, while the
procession bound is real-analytic.  No bridge is fabricated here.
-/

#check S2920HeightLeProcession
#check S2920_thetaLink_generator
#check S2920_thetaLink_unitPower
#check thetaLink
#check thetaLink_generator
#check thetaLink_unitPower
#check LeanFormal.IUT.IUTIV.StepVProcessionAverage.processionAverage_le
#print axioms S2920_thetaLink_generator
#print axioms S2920_thetaLink_unitPower

end LeanFormal.IUT.XiFPaper.S2920ThetaLinkHeight
end
