import tmp.sheaf.xif.paper.S2920ThetaLinkHeight
import tmp.sheaf.xif.paper.S2933PerTripleThetaCertificateActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2920ThetaLinkHeight
open LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2923ThetaLinkBridgeActual

/-- The theta-link unit-power law, expressed on the degree maps. -/
theorem S2923_thetaLink_unitPower_degree
    {U V G H : Type*} [Group U] [Group V] [CommGroup G] [CommGroup H]
    (u : U →* G) (v : V →* H) (q : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hunitG : ∀ a, degreeG (u a) = 1)
    (hunitH : ∀ b, degreeH (v b) = 1)
    (hq : (degreeG q).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0)
    (e : U ≃* V) (a : U) (n : Nat) :
    degreeH (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (unitPowerElement u q a n)) =
      degreeH (unitPowerElement v theta (e a) n) := by
  rw [thetaLink_unitPower]

/-- The theta-link generator law, expressed on the degree maps. -/
theorem S2923_thetaLink_generator_degree
    {U V G H : Type*} [Group U] [Group V] [CommGroup G] [CommGroup H]
    (u : U →* G) (v : V →* H) (q : G) (theta : H)
    (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hunitG : ∀ a, degreeG (u a) = 1)
    (hunitH : ∀ b, degreeH (v b) = 1)
    (hq : (degreeG q).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0)
    (e : U ≃* V) :
    degreeH (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (distinguishedGenerator u q)) =
      degreeH (distinguishedGenerator v theta) := by
  rw [thetaLink_generator]

/-- Per-triple procession real upper bound, using the S2933 certificate. -/
theorem S2923_procession_le_thetaUpper
    (C : S2933Certificate) (a b c : Nat) :
    (1 / (C.n : Real)) *
        ∑ j ∈ Icc 1 C.n,
          collectionBound (2 * (C.n : Real) + 1) S2921D
            (S2921Q a b c) (S2921S a b c) (S2921T a b c) j ≤
      S2933ThetaUpper C.n a b c :=
  S2933_procession_le_thetaUpper C a b c

/-- Per-triple ABC theta upper bound. -/
theorem S2923_thetaUpper_bound
    (C : S2933Certificate) (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) ≤
      6 * (1 + C.eps) * S2792RegionVolume a b c + C.AJ :=
  S2933_thetaUpper_bound C a b c habc

/-- Per-triple certificate yields S2838ThetaUpperGap. -/
theorem S2923_to_S2838ThetaUpperGap (C : S2933Certificate) :
    S2838ThetaUpperGap C.eps C.AJ :=
  S2933_to_S2838ThetaUpperGap C

/-- Exact missing bridge: per-triple height-to-procession estimate. -/
def S2923HeightBridge (n : Nat) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcJInvariant a b c) ≤
      (1 / (n : Real)) *
        ∑ j ∈ Icc 1 n,
          collectionBound (2 * (n : Real) + 1) S2921D
            (S2921Q a b c) (S2921S a b c) (S2921T a b c) j

/-- Conditional bridge consumer. -/
theorem S2923_heightBridge_of_input
    (n : Nat) (h : S2923HeightBridge n) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcJInvariant a b c) ≤
        (1 / (n : Real)) *
          ∑ j ∈ Icc 1 n,
            collectionBound (2 * (n : Real) + 1) S2921D
              (S2921Q a b c) (S2921S a b c) (S2921T a b c) j :=
  h

#check S2923_thetaLink_unitPower_degree
#check S2923_thetaLink_generator_degree
#check S2923_procession_le_thetaUpper
#check S2923_thetaUpper_bound
#check S2923_to_S2838ThetaUpperGap
#check S2923HeightBridge
#print axioms S2923_thetaLink_unitPower_degree
#print axioms S2923_thetaLink_generator_degree
#print axioms S2923_procession_le_thetaUpper
#print axioms S2923_thetaUpper_bound
#print axioms S2923_to_S2838ThetaUpperGap

end LeanFormal.IUT.XiFPaper.S2923ThetaLinkBridgeActual
end
