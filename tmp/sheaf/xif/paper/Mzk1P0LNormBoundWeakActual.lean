/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutProductActual
import tmp.sheaf.xif.paper.Mzk1A1SignedReadoutProductActual
import tmp.sheaf.xif.paper.Mzk1P3ProductHaarPiActual
import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-! # P0-L: weak form of the L bound from the A1 product bound and totalDelta

`thetaNormReadProduct = s1915ClosedForm - 1` (proved) and A1
`productQ_normalizedLog = s1915ClosedForm - 1 - totalDelta`, so
`productQ_normalizedLog <= thetaNormReadProduct` (using `totalDelta >= 0`).  Hence the
L bound follows from a bound against the product normalized log.  This is a WEAK
(global) form: the single-place `d_F` normalization is NOT used here; if `d_F > 1`
one must divide explicitly (`thetaNormReadL` is a1LocalQLog-type, not a1SignedTerm). -/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormBoundWeakActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutProductActual
open LeanFormal.IUT.XiFPaper.Mzk1A1SignedReadoutProductActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open MeasureTheory

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Weak L bound: a bound against the product normalized log plus the A1 totalDelta
nonnegativity implies the bound against `thetaNormReadProduct`. -/
theorem qRead_le_thetaNormReadProduct_of_productBound
    (hQ0 : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤)
    (hdeg : ∀ b, 0 < s1915LocalDegree T b)
    (h : qReadActual I place ≤
      rootExtensionProductNormalizedLog T (c0ProductQ T)) :
    qReadActual I place ≤ thetaNormReadProduct T := by
  have hδ : 0 ≤ totalDelta T :=
    totalDelta_nonneg T hdeg (hQ0 := hQ0) (hQtop := hQtop) (hO0 := hO0) (hOtop := hOtop)
  have hid := productQ_normalizedLog_eq_closedForm_sub_one_sub_totalDelta T
    (hQ0 := hQ0) (hQtop := hQtop) (hO0 := hO0) (hOtop := hOtop) (hd := hdeg)
  have hclosed := thetaNormReadProduct_eq_closedForm_sub_one (T := T)
  linarith

def lNormBoundWeakRows : List (String × String × String) :=
  [ ("qRead_le_thetaNormReadProduct_of_productBound",
      "product-bound + totalDelta >= 0 => thetaNormReadProduct bound",
      "PROVED (conditional on A1 Haar/degree hypotheses)"),
    ("d_F>1", "single-place normalization: thetaNormReadL is a1LocalQLog-type; must divide by d_F explicitly",
      "EXPLICIT GAP (not used)"),
    ("unitMass = 1", "not assumed", "NOT CLAIMED") ]

theorem lNormBoundWeakRows_length : lNormBoundWeakRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0LNormBoundWeakActual

end