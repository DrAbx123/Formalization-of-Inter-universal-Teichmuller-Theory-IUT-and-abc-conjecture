import tmp.sheaf.xif.paper.S2933PerTripleThetaCertificateActual
import tmp.sheaf.xif.paper.S2923ThetaLinkBridgeActual
import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
import LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantHeight

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
open LeanFormal.IUT.XiFPaper.S2923ThetaLinkBridgeActual
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
open LeanFormal.IUT
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2935HeightLeProcessionActual

/-- Exact target: per-triple height-to-procession inequality using the actual
S2921 candidates. -/
def S2935HeightLeProcession (n : Nat) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcJInvariant a b c) ≤
      (1 / (n : Real)) *
        ∑ j ∈ Icc 1 n,
          collectionBound (2 * (n : Real) + 1) S2921D
            (S2921Q a b c) (S2921S a b c) (S2921T a b c) j

/-- Reusable actual: theta-link unit-power law on degree maps (S2923). -/
theorem S2935_thetaLink_unitPower_degree
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
      degreeH (unitPowerElement v theta (e a) n) :=
  S2923_thetaLink_unitPower_degree u v q theta degreeG degreeH hu hv
    hunitG hunitH hq htheta e a n

/-- Reusable actual: theta-link generator law on degree maps (S2923). -/
theorem S2935_thetaLink_generator_degree
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
      degreeH (distinguishedGenerator v theta) :=
  S2923_thetaLink_generator_degree u v q theta degreeG degreeH hu hv
    hunitG hunitH hq htheta e

/-- Reusable actual: S2752 weight/volume inequality, the only actual
arithmetic comparison feeding the candidates. -/
theorem S2935_hweightvol (a b c : Nat) (habc : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) ≤ S2921Q a b c :=
  S2921_hweightvol_candidate a b c habc

/-- Actual ABC J-height upper bound from ABCInvariantHeight. -/
theorem S2935_Jheight_upper (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) ≤ 6 * Real.log (c : Real) + Real.log 256 :=
  abcJInvariant_logHeight_le habc

/-- Conditional reduction: it suffices to bound the explicit elementary upper
bound 6 log c + log 256 by the procession average. -/
theorem S2935_height_le_procession_of_elementary
    (n : Nat)
    (h : ∀ a b c : Nat, IsABCTriple a b c →
      6 * Real.log (c : Real) + Real.log 256 ≤
        (1 / (n : Real)) *
          ∑ j ∈ Icc 1 n,
            collectionBound (2 * (n : Real) + 1) S2921D
              (S2921Q a b c) (S2921S a b c) (S2921T a b c) j) :
    S2935HeightLeProcession n := by
  intro a b c habc
  exact le_trans (S2935_Jheight_upper a b c habc) (h a b c habc)

/-!
## First error

The target S2935HeightLeProcession is a J-height upper bound by the procession
average.  The actual reusable material is:

* S2923_thetaLink_unitPower_degree / S2923_thetaLink_generator_degree:
  algebraic degree laws of thetaLink;
* S2752_hweightvol: arithmeticWeight <= S2921Q;
* S2833_region_volume / S2792_regionVolume_le_weight_add_D: volume and
  weight/region comparisons;
* S2838_height_le_Jlog: a LOWER bound for the J-height in terms of the point
  height, not an upper bound.

None of these gives
  logHeight J <= (1/n) * sum collectionBound(D,Q,S,T,j).

The degree laws are about multiplicative degrees of thetaLink monoid elements;
they contain no Height.logHeight₁ and no collectionBound.  This is exactly the
missing analytic/geometric bridge already isolated in S2920/S2921.

No new certificate is introduced; no upper estimate is fabricated.
-/

#check S2935HeightLeProcession
#check S2935_thetaLink_unitPower_degree
#check S2935_thetaLink_generator_degree
#check S2935_hweightvol
#check S2838_height_le_Jlog
#check S2935_Jheight_upper
#check S2935_height_le_procession_of_elementary
#check abcJInvariant_logHeight_le
#check S2792_regionVolume_le_weight_add_D
#print axioms S2935_thetaLink_unitPower_degree
#print axioms S2935_thetaLink_generator_degree
#print axioms S2935_hweightvol

end LeanFormal.IUT.XiFPaper.S2935HeightLeProcessionActual
end
