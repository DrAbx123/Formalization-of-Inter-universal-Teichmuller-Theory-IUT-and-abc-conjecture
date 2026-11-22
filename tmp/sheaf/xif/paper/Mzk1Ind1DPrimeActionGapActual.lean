import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1DPrimeActionGapActual
open LeanFormal.IUT

universe u v uM
variable {V : Type v}

/-- The missing action datum on a D-prime-strip: an actual multiplicative
monoid `M v` together with an action of the local group `D.Pi v` on it. -/
structure DPrimeStripActionData (D : DPrimeStrip.{u} V) (M : V → Type uM)
    [∀ v, CommMonoid (M v)] where
  action : ∀ v, D.Pi v →* MulAut (M v)

/-- An `FPrimeStrip` supplies the missing action datum for its own Mon. -/
def fPrimeStripActionData (F : FPrimeStrip.{u, v} V) :
    DPrimeStripActionData F.toD F.Mon where
  action := F.action

/-- The Galois-fixed/torsion/infinitely-divisible route data.  It records the
actual multiplicative action, the Galois-fixed subgroup, the torsion quotient,
and the subgroup intended to be extracted by the `r != p` infinite-divisibility
condition.  No inhabitant is supplied. -/
structure Ind1GaloisFixedRoute (D : DPrimeStrip.{u} V) where
  M : V → Type uM
  [commMonoid : ∀ v, CommMonoid (M v)]
  actionData : DPrimeStripActionData D M
  fixedSubgroup : ∀ v, Subgroup (M v)
  modTorsion : ∀ v, Type
  integralLayer : ∀ v, Subgroup (M v)

def Ind1GaloisFixedRouteRequired (D : DPrimeStrip.{u} V) : Prop :=
  Nonempty (Ind1GaloisFixedRoute D)

#print axioms fPrimeStripActionData
end LeanFormal.IUT.XiFPaper.Mzk1Ind1DPrimeActionGapActual