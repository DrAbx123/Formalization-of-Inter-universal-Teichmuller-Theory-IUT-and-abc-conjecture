import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import tmp.sheaf.xif.paper.Mzk1Ind1InfiniteDivisibleActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisFixedRouteActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Ind1InfiniteDivisibleActual

universe u v
variable {V : Type v}

/-- Units fixed by the actual `FPrimeStrip.action` of `Pi v`. -/
def actionFixedUnits (F : FPrimeStrip.{u, v} V) (v : V) :
    Subgroup ((F.Mon v)ˣ) where
  carrier := {x | ∀ g : F.toD.Pi v, Units.mapEquiv (F.action v g) x = x}
  one_mem' := by intro g; simp
  mul_mem' := by
    intro x y hx hy g
    rw [map_mul, hx g, hy g]
  inv_mem' := by
    intro x hx g
    rw [map_inv, hx g]

theorem mem_actionFixedUnits (F : FPrimeStrip.{u, v} V) (v : V)
    (x : (F.Mon v)ˣ) :
    x ∈ actionFixedUnits F v ↔
      ∀ g : F.toD.Pi v, Units.mapEquiv (F.action v g) x = x := Iff.rfl

/-- The image of the fixed units in the torsion quotient. -/
def actionFixedUnitsInTorsion (F : FPrimeStrip.{u, v} V) (v : V) :
    Subgroup (TimesMuQuotient ((F.Mon v)ˣ)) :=
  (actionFixedUnits F v).map (TimesMuQuotient.quotientMap)

/-- Exact route obstruction: the extracted integral-unit layer inside the
torsion quotient is not supplied by the tree.  This structure records the
missing data without a bare closing `Prop`. -/
structure Ind1IntegralExtraction (F : FPrimeStrip.{u, v} V) where
  integralLayer : ∀ v, Subgroup (TimesMuQuotient ((F.Mon v)ˣ))
  containsFixedUnits : ∀ v,
    actionFixedUnitsInTorsion F v ≤ integralLayer v

def Ind1IntegralExtractionRequired (F : FPrimeStrip.{u, v} V) : Prop :=
  Nonempty (Ind1IntegralExtraction F)

#print axioms mem_actionFixedUnits

/-- Candidate extraction: the infinitely divisible subgroup in degree `r`
inside the torsion quotient. -/
def candidateIntegralLayer (F : FPrimeStrip.{u, v} V) (v : V) (r : Nat) :
    Subgroup (TimesMuQuotient ((F.Mon v)ˣ)) :=
  infinitelyDivisibleSubgroup (G := TimesMuQuotient ((F.Mon v)ˣ)) r

theorem candidateIntegralLayer_mem (F) (v) (r)
    (x : TimesMuQuotient ((F.Mon v)ˣ)) :
    x ∈ candidateIntegralLayer F v r ↔
      InfinitelyDivisibleFor r x := Iff.rfl

/-- Exact proof obligation for the candidate extraction. -/
def Ind1IntegralExtractionCandidateGap
    (F : FPrimeStrip.{u, v} V) (r : Nat) : Prop :=
  ∀ v : V, actionFixedUnitsInTorsion F v ≤ candidateIntegralLayer F v r

def Ind1IntegralExtraction_of_candidate
    (F : FPrimeStrip.{u, v} V) (r : Nat)
    (h : Ind1IntegralExtractionCandidateGap F r) :
    Ind1IntegralExtraction F where
  integralLayer v := candidateIntegralLayer F v r
  containsFixedUnits v := h v

#print axioms candidateIntegralLayer_mem
end LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisFixedRouteActual