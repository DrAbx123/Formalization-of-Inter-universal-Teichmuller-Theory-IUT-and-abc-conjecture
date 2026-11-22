import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import tmp.sheaf.xif.paper.Mzk1Ind1InfiniteDivisibleActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1CorrectedExtractionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Ind1InfiniteDivisibleActual

universe u v
variable {V : Type v} {F : FPrimeStrip.{u, v} V}

/-- Action of the local group on the units of the multiplicative monoid. -/
def unitAction (F : FPrimeStrip.{u, v} V) (v : V) :
    F.toDPrimeStrip.Pi v →* MulAut ((F.Mon v)ˣ) where
  toFun g := Units.mapEquiv (F.action v g)
  map_one' := by ext; simp
  map_mul' := by
    intro g h
    ext x
    change (F.action v (g * h)) (x : F.Mon v) =
      (F.action v g) ((F.action v h) (x : F.Mon v))
    rw [map_mul]
    rfl

/-- Fixed-unit subgroup for an arbitrary subgroup `H` (openness is an extra
condition supplied later). -/
def unitFixedSubgroup (F : FPrimeStrip.{u, v} V) (v : V)
    (H : Subgroup (F.toDPrimeStrip.Pi v)) : Subgroup ((F.Mon v)ˣ) where
  carrier := {x | ∀ g : H, unitAction F v (g : F.toDPrimeStrip.Pi v) x = x}
  one_mem' := by intro g; simp
  mul_mem' := by intro x y hx hy g; rw [map_mul, hx g, hy g]
  inv_mem' := by intro x hx g; rw [map_inv, hx g]

/-- `A_H`: the image of the fixed units in the torsion quotient. -/
def invariantUnitLayer (F : FPrimeStrip.{u, v} V)
    (H : ∀ v, Subgroup (F.toDPrimeStrip.Pi v)) (v : V) :
    Subgroup (TimesMuQuotient ((F.Mon v)ˣ)) :=
  (unitFixedSubgroup F v (H v)).map TimesMuQuotient.quotientMap

/-- Corrected depth layer: `D_r` inside `A_H`, then map back to ambient. -/
def correctedDepthLayer (F : FPrimeStrip.{u, v} V)
    (H : ∀ v, Subgroup (F.toDPrimeStrip.Pi v)) (r : Nat) (v : V) :
    Subgroup (TimesMuQuotient ((F.Mon v)ˣ)) :=
  (infinitelyDivisibleSubgroup (G := invariantUnitLayer F H v) r).map
    (invariantUnitLayer F H v).subtype

structure Ind1CorrectedExtraction (F : FPrimeStrip.{u, v} V) where
  H : ∀ v, Subgroup (F.toDPrimeStrip.Pi v)
  r : Nat
  hr : 2 ≤ r
  integralLayer : ∀ v, Subgroup (TimesMuQuotient ((F.Mon v)ˣ))
  integralLayer_eq : ∀ v,
    integralLayer v = correctedDepthLayer F H r v

def Ind1CorrectedExtractionRequired (F : FPrimeStrip.{u, v} V) : Prop :=
  Nonempty (Ind1CorrectedExtraction F)


#print axioms invariantUnitLayer
#print axioms correctedDepthLayer
end LeanFormal.IUT.XiFPaper.Mzk1Ind1CorrectedExtractionActual