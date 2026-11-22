import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-!
# shehdd A654/A657 scaling-direction study and Gap1 test (Sha)

Scaling direction / correction candidate for the triple-dependent region:
* generic REAL scalar scaling `scaleMap r x = r • x` is bijective for `r ≠ 0`
  (modules over ℝ);
* generic NAT scalar scaling `scaleMapNat n x = n • x` (no module structure needed)
  with composition law `scaleMapNat m (scaleMapNat n x) = (m*n) • x`;
  the canonical triple scale is exactly `scaleMapNat (a+b+c+1)`;
* **Gap1 direction test**: if a comparison region stays inside the finite-log-volume
  unit region (as with a shrinking/inverse scaling), Gap1 is IMPOSSIBLE, because
  unbounded heights would be bounded by the fixed unit-region log-volume.
  Hence the scaling direction for Gap 1 must not shrink the region.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1GapScalingDirectionShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

section GenericScaling

variable {X : Type*} [AddCommGroup X] [Module Real X]

/-- Generic real scalar scaling map. -/
def scaleMap (r : Real) (x : X) : X := r • x

theorem scaleMap_comp_inv (r : Real) (hr : r ≠ 0) :
    scaleMap (X := X) r⁻¹ ∘ scaleMap r = id := by
  funext x
  change r⁻¹ • (r • x) = x
  rw [smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem scaleMap_injective (r : Real) (hr : r ≠ 0) :
    Function.Injective (scaleMap (X := X) r) := by
  intro x y h
  have h' : r • x = r • y := h
  calc x = r⁻¹ • (r • x) := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
    _ = r⁻¹ • (r • y) := by rw [h']
    _ = y := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem scaleMap_surjective (r : Real) (hr : r ≠ 0) :
    Function.Surjective (scaleMap (X := X) r) :=
  fun y => ⟨r⁻¹ • y, by
    change r • (r⁻¹ • y) = y
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]⟩

theorem scaleMap_bijective (r : Real) (hr : r ≠ 0) :
    Function.Bijective (scaleMap (X := X) r) :=
  ⟨scaleMap_injective r hr, scaleMap_surjective r hr⟩

end GenericScaling

section NatScaling

variable {X : Type*} [AddCommMonoid X]

/-- Generic NAT scalar scaling map (works for any additive monoid). -/
def scaleMapNat (n : Nat) (x : X) : X := n • x

theorem scaleMapNat_mul (m n : Nat) (x : X) :
    scaleMapNat m (scaleMapNat n x) = (m * n) • x := by
  unfold scaleMapNat
  rw [← smul_smul]

end NatScaling

section GapDirection

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The canonical triple scale is the NAT multiplicative (growing) direction. -/
theorem canonical_tripleScale_eq_scaleMapNat (a b c : Nat) :
    tripleScale T a b c =
      scaleMapNat (X := S1902Carrier T) (a + b + c + 1) :=
  rfl

/-- **Gap 1 direction test**: if every comparison region stays in the finite-log-volume
unit region, Gap 1 cannot hold (the region cannot supply an unbounded log-volume). -/
theorem gap1_impossible_of_region_in_unitRegion
    {X : Type*} (W : IQHullLogVolumeInterface X)
    (hunit : W.logVolume W.unitRegion < ⊤)
    (region : Nat → Nat → Nat → Set X)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.unitRegion) :
    ¬ Gap1Prop W region := by
  intro h
  have hbnd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * (W.logVolume W.unitRegion).toReal := by
    intro a b c htriple
    have h1 := h 1 zero_lt_one a b c htriple
    have hle : (W.logVolume (region a b c)).toReal ≤
        (W.logVolume W.unitRegion).toReal :=
      ENNReal.toReal_mono (ne_of_lt hunit) (W.logVolume_mono (hsub a b c htriple))
    nlinarith
  obtain ⟨a, b, c, habc, hgt⟩ := abcRationalPoint_logHeight_unbounded
    (2 * (W.logVolume W.unitRegion).toReal)
  exact not_lt_of_ge (hbnd a b c habc) hgt

end GapDirection

structure ScalingDirectionRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def scalingDirectionRows : List ScalingDirectionRow :=
  [ ⟨"generic scale bijectivity", "scaleMap r bijective for r != 0; inverse scaleMap r^-1", "GREEN"⟩
  , ⟨"nat scale composition", "scaleMapNat m (scaleMapNat n x) = (m*n) smul x", "GREEN"⟩
  , ⟨"canonical direction", "tripleScale = scaleMapNat (a+b+c+1): growing, not shrinking", "GREEN"⟩
  , ⟨"Gap1 direction test", "region inside finite unit region => Gap1 impossible", "GREEN"⟩
  , ⟨"correction candidate", "inverse/shrinking scaling cannot support Gap1; multiplicative >=1 direction needed", "AUDIT"⟩
  , ⟨"scope", "direction study only; named gaps unchanged", "INTEGRITY"⟩
  ]

theorem scalingDirectionRows_length : scalingDirectionRows.length = 6 := rfl

theorem scalingDirectionRows_statuses_ok :
    scalingDirectionRows.all (fun r =>
      r.status ∈ ["GREEN", "AUDIT", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1GapScalingDirectionShaActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapScalingDirectionShaActual.gap1_impossible_of_region_in_unitRegion
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapScalingDirectionShaActual.scaleMap_bijective
