import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1GapReductionSourceActual — IUT IV §2 reduced-gap source data -> comparison -> ABC bridge

DAG node: iutiv-abc:GapReduction (REDUCED-input assembly, CONDITIONAL, 0 unproved deps).
Core Cor312ComparisonGapReduction assembles the two comparison gaps from six reduced
inputs (valuation bound, weight/volume, unit normalization, split, point finiteness,
point bound).  This file packages those inputs as an explicit per-epsilon structure
and gives the source-facing consumers: comparison data at fixed eps, the bridge
interface for a per-epsilon family, and ABCConjecture.  No gap field is proved;
the reduced inputs remain named.

No closure claim; GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GapReductionSourceActual

open LeanFormal.IUT

universe u

/-- Explicit reduced inputs for one epsilon of the IUT IV §2 gap assembly. -/
structure Cor312ReducedGapData {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (eps : Real) where
  D₀ : Real
  D₁ : Real
  hD₀ : 0 ≤ D₀
  hval : ∀ a b c : Nat, IsABCTriple a b c →
    ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
      max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps
  hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
    arithmeticWeight (abcRationalPoint a c) ≤
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal
  hunit : W.logVolume W.unitRegion ≤ W.logVolume W.hull + ENNReal.ofReal D₀
  hsplit : ∀ a b c : Nat, IsABCTriple a b c →
    W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
      W.logVolume (W.scaleShift '' W.unitRegion) +
        W.logVolume {W.scaleShift (logShellPoint a b c)}
  hptfin : ∀ a b c : Nat, IsABCTriple a b c →
    W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤
  hpoint : ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁

/-- Assemble the per-epsilon comparison from explicit reduced gap data. -/
def epsilonComparison_of_reducedData {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat → Nat → Nat → X} {eps : Real}
    (D : Cor312ReducedGapData W logShellPoint eps) (heps : 0 ≤ eps) :
    Cor312EpsilonArithmeticComparison W eps :=
  cor312GapAssembly_epsilonComparisonOfReducedInputs W logShellPoint heps D.hD₀
    D.hval D.hweightvol D.hunit D.hsplit D.hptfin D.hpoint

/-- A bridge interface from a per-epsilon reduced-gap family. -/
def bridgeInterface_of_reducedFamily (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (F : ∀ eps : Real, 0 < eps → Cor312ReducedGapData W logShellPoint eps) :
    Cor312ToABCBridgeInterface.{u} :=
{ carrier := X
  hullData := W
  epsilonComparison := fun eps heps =>
    epsilonComparison_of_reducedData (F eps heps) (le_of_lt heps) }

/-- ABC from a per-epsilon reduced-gap family (conditional). -/
theorem abcConjecture_of_reducedFamily (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (F : ∀ eps : Real, 0 < eps → Cor312ReducedGapData W logShellPoint eps) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (bridgeInterface_of_reducedFamily X W logShellPoint F)

/-- Rows: reduced-gap source-data status. -/
def gapReductionSourceRows : List (String × String × String) :=
  [ ("reduced inputs structure", "Cor312ReducedGapData", "DEF (six named inputs + constants)"),
    ("assembly", "epsilonComparison_of_reducedData", "DEF (core assembly consumer)"),
    ("bridge/ABC", "bridgeInterface_of_reducedFamily / abcConjecture_of_reducedFamily", "PROVED (conditional)"),
    ("gaps", "N1/N2 remain named; no gap field proved", "NAMED"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem gapReductionSourceRows_length : gapReductionSourceRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GapReductionSourceActual

end
