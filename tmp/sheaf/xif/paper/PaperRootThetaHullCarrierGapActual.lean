import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

/-!
# Root-valued Theta image and exact tensor-hull carrier gap

Paper theta values are q_v^(j^2) with q_v = q^(1/2l).  The actual root units live
in the product of algebraic closures of the completions
(PaperC3ThetaRootActual.RootThetaCarrier).  The completion-valued
qUnit^(j^2) image and its lambda-O hull are not the paper theta hull.

This file keeps the actual nonzero root-valued Theta image set, proves its
subset relation, and records the exact missing object: a tensor-packet lift of
the extension-valued root units together with a unit reference and a lambda-O
hull on that lifted carrier.  No fake extension tensor or completion surrogate is
used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootThetaHullCarrierGapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Actual nonzero root-valued Theta image set in the algebraic-closure product. -/
noncomputable def paperNonzeroRootThetaImageSet :
    Set (RootThetaCarrier (G := G)) :=
  {x | ∃ j : ThetaLabel (l := l),
    x = paperRootThetaImagePointTheta (G := G) j}

/-- The nonzero root image is contained in the full root image set. -/
theorem paperNonzeroRootThetaImageSet_subset :
    paperNonzeroRootThetaImageSet (G := G) ⊆
      paperRootThetaImageSet (G := G) := by
  rintro x ⟨j, rfl⟩
  exact paperRootThetaImagePointTheta_mem (G := G) j

/-- The actual root theta unit is a 2l-th root of the qUnit power; the
completion qUnit^(j^2) is not the root theta value. -/
theorem paperRootThetaUnit_pow_twoL_eq (j : SignedLabel l.value) (v : V) :
    paperRootThetaUnit (G := G) j v ^ (2 * l.value) =
      (unitToAlgClosed (G.qUnit v)) ^ (gaussExponent j.1).toNat :=
  paperRootThetaUnit_pow_twoL (G := G) j v

/-- Exact missing lift: a tensor carrier with an actual unit reference and a
lambda-O hull carrying the extension-valued root Theta image. -/
structure RootThetaTensorHullCarrierGap where
  tensorCarrier : Type
  imageMap : RootThetaCarrier (G := G) → tensorCarrier
  imageSet : Set tensorCarrier
  imageSet_eq : imageSet = imageMap '' paperNonzeroRootThetaImageSet (G := G)
  unitReference : Set tensorCarrier
  lambdaHull : Set tensorCarrier
  image_subset_hull : imageSet ⊆ lambdaHull
  carrier_compat : Prop

/-- Exact missing root tensor-hull carrier. -/
def RootThetaTensorHullCarrierGapRequired : Prop :=
  Nonempty (RootThetaTensorHullCarrierGap (G := G))

end LeanFormal.IUT.XiFPaper.PaperRootThetaHullCarrierGapActual

end
