import tmp.sheaf.xif.paper.PaperRootThetaProductCarrierActual
import tmp.sheaf.xif.paper.PaperRootExtensionEquivActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure

/-! # Actual root Theta norm bound -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootThetaNormBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionEquivActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaProductCarrierActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Norm of a root-extension unit, computed after the actual carrier
equivalence in the source spectral-norm carrier. -/
noncomputable def rootExtensionUnitNorm (v : V)
    (u : (RootExtension (G := G) v)ˣ) : Real :=
  ‖((rootExtensionEquivUnits (G := G) v u :
      (SourceAlgebraicClosure (G.place v).val)ˣ) :
      SourceAlgebraicClosure (G.place v).val)‖

/-- The transported unit norm is nonnegative. -/
theorem rootExtensionUnitNorm_nonneg (v : V)
    (u : (RootExtension (G := G) v)ˣ) :
    0 ≤ rootExtensionUnitNorm (G := G) v u := by
  unfold rootExtensionUnitNorm
  exact norm_nonneg _

/-- The transported unit norm is multiplicative on powers. -/
theorem rootExtensionUnitNorm_pow (v : V)
    (u : (RootExtension (G := G) v)ˣ) (n : Nat) :
    rootExtensionUnitNorm (G := G) v (u ^ n) =
      rootExtensionUnitNorm (G := G) v u ^ n := by
  unfold rootExtensionUnitNorm
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow]

/-- The transported norm of the unitToAlgClosed qUnit is at most one. -/
theorem rootExtensionUnitNorm_unitToAlgClosed_le_one
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1)
    (v : V) :
    rootExtensionUnitNorm (G := G) v (unitToAlgClosed (G.qUnit v)) ≤ 1 := by
  unfold rootExtensionUnitNorm
  let qEl : SourceAlgebraicClosure (G.place v).val :=
    algebraMap (NormalizedCompletion (G.place v).val)
      (SourceAlgebraicClosure (G.place v).val)
      ((G.qUnit v : G.valueCarrier v) : CommonPrimeCompletion (G.place v))
  change ‖(qEl)‖ ≤ 1
  have hnormeq : ‖(qEl)‖ =
      ‖(((G.qUnit v : G.valueCarrier v) :
        CommonPrimeCompletion (G.place v)))‖ := by
    dsimp only [qEl]
    rw [norm_algebraMap']
    rfl
  rw [hnormeq]
  exact hq v

/-- The 2l-th root has transported norm at most one. -/
theorem twoLthRootAt_norm_le_one
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1)
    (v : V) :
    rootExtensionUnitNorm (G := G) v (twoLthRootAt (G := G) v) ≤ 1 := by
  have h2l : 2 * l.value ≠ 0 := by
    exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hpow : rootExtensionUnitNorm (G := G) v (twoLthRootAt (G := G) v) ^ (2 * l.value)
      = rootExtensionUnitNorm (G := G) v (unitToAlgClosed (G.qUnit v)) := by
    rw [← rootExtensionUnitNorm_pow]
    rw [twoLthRootAt_pow]
  have hle : rootExtensionUnitNorm (G := G) v (twoLthRootAt (G := G) v) ^ (2 * l.value) ≤ 1 := by
    rw [hpow]
    exact rootExtensionUnitNorm_unitToAlgClosed_le_one (G := G) hq v
  exact (pow_le_one_iff_of_nonneg (rootExtensionUnitNorm_nonneg (G := G) v (twoLthRootAt (G := G) v)) h2l).mp hle

/-- The paper root theta unit has transported norm at most one. -/
theorem paperRootThetaUnit_norm_le_one
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1)
    (j : ThetaLabel (l := l)) (v : V) :
    rootExtensionUnitNorm (G := G) v
      (paperRootThetaImagePointTheta (G := G) j v) ≤ 1 := by
  have hroot := twoLthRootAt_norm_le_one (G := G) hq v
  unfold paperRootThetaImagePointTheta paperRootThetaImagePoint paperRootThetaUnit
  rw [rootExtensionUnitNorm_pow]
  exact pow_le_one₀ (rootExtensionUnitNorm_nonneg (G := G) v (twoLthRootAt (G := G) v)) hroot

/-- Unconditional root image containment in the product unit ball, from hq. -/
theorem rootThetaProductImageSet_subset_unitBall_of_hq
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    rootThetaProductImageSet (G := G) ⊆ rootThetaUnitBall (G := G) :=
  rootThetaProductImageSet_subset_unitBall (G := G)
    (fun j v => by
      simpa [rootExtensionUnitNorm] using
        paperRootThetaUnit_norm_le_one (G := G) hq j v)

end LeanFormal.IUT.XiFPaper.PaperRootThetaNormBoundActual

end