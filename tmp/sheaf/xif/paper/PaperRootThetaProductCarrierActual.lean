import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure
import tmp.sheaf.xif.paper.PaperRootExtensionEquivActual

/-!
# Product sup-norm carrier for the root-valued Theta units

The root theta units live in the product of algebraic closures of the actual
completions.  There is no Haar measure on the full algebraic closure, so this
file constructs the actual product carrier with the sup norm and its unit ball.
The actual root image is shown to land in the unit ball under the exact root norm
bound.  The absent product Haar/measure is recorded as an exact API gap, not
faked.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootThetaProductCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionEquivActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Product carrier of the actual algebraic-closure root units, with the
source spectral norm on each factor. -/
abbrev RootThetaProductCarrier : Type (max u v) :=
  (v : V) → (SourceAlgebraicClosure (G.place v).val)ˣ

/-- Product sup norm of a root unit family. -/
noncomputable def rootSupNorm (x : RootThetaProductCarrier (G := G)) : NNReal :=
  Finset.univ.sup (fun v : V =>
    ⟨‖((x v : (SourceAlgebraicClosure (G.place v).val)ˣ) :
      SourceAlgebraicClosure (G.place v).val)‖, norm_nonneg _⟩)

/-- Actual product unit ball: sup norm at most one. -/
def rootThetaUnitBall : Set (RootThetaProductCarrier (G := G)) :=
  {x | rootSupNorm (G := G) x ≤ 1}

/-- Actual root theta image point in the product carrier. -/
noncomputable def rootThetaProductImagePoint
    (j : ThetaLabel (l := l)) : RootThetaProductCarrier (G := G) :=
  fun v => rootExtensionEquivUnits (G := G) v
    (paperRootThetaImagePointTheta (G := G) j v)

/-- Actual root theta image set in the product carrier. -/
noncomputable def rootThetaProductImageSet :
    Set (RootThetaProductCarrier (G := G)) :=
  Set.range (rootThetaProductImagePoint (G := G))

/-- Exact root norm bound needed for the unit-ball containment. -/
def RootThetaRootNormBound : Prop :=
  ∀ (j : ThetaLabel (l := l)) (v : V),
    ‖((rootExtensionEquivUnits (G := G) v
      (paperRootThetaImagePointTheta (G := G) j v) :
      (SourceAlgebraicClosure (G.place v).val)ˣ) :
      SourceAlgebraicClosure (G.place v).val)‖ ≤ 1

/-- Under the exact root norm bound, the root theta image lies in the actual
product unit ball. -/
theorem rootThetaProductImageSet_subset_unitBall
    (hroot : RootThetaRootNormBound (G := G)) :
    rootThetaProductImageSet (G := G) ⊆ rootThetaUnitBall (G := G) := by
  rintro x ⟨j, rfl⟩
  unfold rootThetaUnitBall rootSupNorm rootThetaProductImagePoint
  change (Finset.univ.sup (fun v : V =>
    (⟨‖(((rootExtensionEquivUnits (G := G) v)
      (paperRootThetaImagePointTheta (G := G) j v) :
      (SourceAlgebraicClosure (G.place v).val)ˣ) :
      SourceAlgebraicClosure (G.place v).val)‖, norm_nonneg _⟩ : NNReal)) : NNReal) ≤ 1
  apply Finset.sup_le
  intro v _
  exact hroot j v

/-- Exact missing product Haar/measure API on the algebraic-closure product. -/
structure RootThetaProductMeasureGap where
  productMeasure : Type
  measurePos : Prop
  measureLtTop : Prop
  rootImage_measurable : Prop

/-- Exact missing product Haar/measure object. -/
def RootThetaProductMeasureGapRequired : Prop :=
  Nonempty (RootThetaProductMeasureGap)

end LeanFormal.IUT.XiFPaper.PaperRootThetaProductCarrierActual

end