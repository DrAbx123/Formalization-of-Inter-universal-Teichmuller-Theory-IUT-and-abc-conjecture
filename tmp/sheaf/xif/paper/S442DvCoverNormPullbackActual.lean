import Mathlib.RingTheory.Norm.Basic
import tmp.sheaf.xif.paper.DvTriangleFieldCoversActual
import tmp.sheaf.xif.paper.S433Example32RationalDivisorActual

/-!
# S442: norm pullback on finite etale field covers

For a K-algebra map f : L -> L' between field covers, view L' as an L-algebra
and use Algebra.norm L : L' ->* L.  Units.map gives the actual pullback

  normPullback f : L'^× ->* L^×.

No finite-free hypothesis is needed for the monoid map; the norm compatibility
with the S412 normalized valuations on L and L', which is what S433 needs for
divisor naturality, is recorded as the exact missing datum.

No fake valuation or divisor naturality.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

namespace LeanFormal.IUT.XiFPaper.S442DvCoverNormPullbackActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual

universe u

variable {K : Type u} [Field K]
variable {L L' : Type u} [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- Norm pullback along a K-algebra map: L'^× -> L^×, using L'-as-L-algebra. -/
noncomputable def normPullback (f : L →ₐ[K] L') : L'ˣ →* Lˣ :=
  letI : Algebra L L' := f.toRingHom.toAlgebra
  Units.map (Algebra.norm L)

/-- The norm pullback is the norm of the underlying element. -/
theorem normPullback_apply (f : L →ₐ[K] L') (x : L'ˣ) :
    (normPullback f x : L) =
      letI : Algebra L L' := f.toRingHom.toAlgebra
      Algebra.norm L (x : L') := rfl

/-- Norm pullback is multiplicative. -/
theorem normPullback_mul (f : L →ₐ[K] L') (x y : L'ˣ) :
    normPullback f (x * y) = normPullback f x * normPullback f y :=
  map_mul _ x y

/-- Norm pullback sends 1 to 1. -/
theorem normPullback_one (f : L →ₐ[K] L') :
    normPullback f (1 : L'ˣ) = 1 :=
  map_one _

/-- Exact missing compatibility: the norm pullback agrees with the S412
normalized valuations on the two covers.  This is the norm-valuation formula
needed by S433 divisor naturality. -/
structure DvCoverNormValuationCompatibility
    (V : DvCoverNormalizedValuationData K L)
    (V' : DvCoverNormalizedValuationData K L')
    (f : L →ₐ[K] L') : Prop where
  norm_valuation : ∀ x : L'ˣ,
    V.valuation (normPullback f x) = V'.valuation x

/-- Exact missing norm-valuation compatibility datum. -/
def DvCoverNormValuationCompatibilityRequired
    (V : DvCoverNormalizedValuationData K L)
    (V' : DvCoverNormalizedValuationData K L')
    (f : L →ₐ[K] L') : Prop :=
  Nonempty (DvCoverNormValuationCompatibility V V' f)

/-- S398 cover-level norm pullback for an explicit K-algebra map of underlying
fields. -/
noncomputable def dvTriangleNormPullback
    (L L' : DvTriangleFieldCover K)
    [Field L.obj.obj] [Algebra K L.obj.obj]
    [Field L'.obj.obj] [Algebra K L'.obj.obj]
    (f : L.obj.obj →ₐ[K] L'.obj.obj) :
    L'.obj.objˣ →* L.obj.objˣ :=
  normPullback f

/-- S398 cover-level norm-valuation compatibility exact gap. -/
def DvTriangleCoverNormValuationCompatibilityRequired
    (L L' : DvTriangleFieldCover K)
    [Field L.obj.obj] [Algebra K L.obj.obj]
    [Field L'.obj.obj] [Algebra K L'.obj.obj]
    (V : DvCoverNormalizedValuationData K L.obj.obj)
    (V' : DvCoverNormalizedValuationData K L'.obj.obj)
    (f : L.obj.obj →ₐ[K] L'.obj.obj) : Prop :=
  Nonempty (DvCoverNormValuationCompatibility V V' f)

end LeanFormal.IUT.XiFPaper.S442DvCoverNormPullbackActual

end
