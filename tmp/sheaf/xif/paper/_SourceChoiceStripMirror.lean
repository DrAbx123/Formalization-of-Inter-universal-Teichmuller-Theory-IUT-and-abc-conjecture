import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialIplLinkWiring

/-! # Source choice -> actual F-prime-strip, first actual step

For an arbitrary source input `I : OriginalInput l V` (no concrete
SourceDefinition31Data is constructed), define the actual F-prime-strip
attached to a processor choice `i : I.family.index` by evaluating the
source lattice strip `I.fPrimeStripAt` at the pair `I.index_equiv i`.

This is the minimal actual map required before any SourceRun/evaluation
operation on `Choice = I.family.index`.  The family links `I.fLinkAt` are
the actual operation arrows on these strips.

NOT constructed here (exact first gap): the source evaluation operation
itself (upperEnv provenance) and its forget relation to
`runAlgorithm`'s reduced output.  The reduced output type has no modeled
correspondence to `FPrimeStrip V`; W.3 in
`SourceMultiradialPresentationWiring.lean` records that boundary.
-/

noncomputable section

namespace LeanFormal.IUT.IUTIII.Theorem311.Output

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput l V)

/-- Actual F-prime-strip attached to a processor choice. -/
noncomputable def stripOfChoice
    (I : OriginalInput l V)
    (i : I.family.index) : FPrimeStrip.{umon, uv, upi} V :=
  I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2

@[simp] theorem stripOfChoice_apply
    (I : OriginalInput l V) (i : I.family.index) :
    stripOfChoice I i =
      I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2 := rfl

theorem stripOfChoice_indexOf
    (I : OriginalInput l V) (n m : Int) :
    stripOfChoice I (I.indexOf n m) = I.fPrimeStripAt n m := by
  unfold stripOfChoice
  rw [I.indexOf_apply]

/-- Actual family link arrow between two choice strips. -/
noncomputable def linkOfChoice
    (I : OriginalInput l V)
    (i j : I.family.index) :
    FPrimeStripEquiv (stripOfChoice I i) (stripOfChoice I j) :=
  I.fLinkAt (I.index_equiv i).1 (I.index_equiv i).2
    (I.index_equiv j).1 (I.index_equiv j).2

theorem linkOfChoice_refl
    (I : OriginalInput l V) (i : I.family.index) :
    linkOfChoice I i i = FPrimeStripEquiv.refl (stripOfChoice I i) := by
  unfold linkOfChoice stripOfChoice
  exact I.fLinkAt_refl _ _

theorem linkOfChoice_trans
    (I : OriginalInput l V)
    (i j k : I.family.index) :
    FPrimeStripEquiv.trans (linkOfChoice I i j) (linkOfChoice I j k) =
      linkOfChoice I i k := by
  unfold linkOfChoice
  exact I.fLinkAt_trans _ _ _ _ _ _

end LeanFormal.IUT.IUTIII.Theorem311.Output

end
