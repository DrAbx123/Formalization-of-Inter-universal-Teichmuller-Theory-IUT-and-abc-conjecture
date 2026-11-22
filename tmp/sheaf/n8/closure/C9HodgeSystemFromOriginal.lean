import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge

/-! # First raw-data construction from OriginalInput

Builds the actual `SourceHodgeTheaterSystem` from the Hodge-theater family in
`OriginalInput`. The link is the prime-strip transport supplied by the family
link; q/scale and permutation data are the actual theta packets.

No toy Hodge theater and no Input/Completion field are used.
-/

namespace LeanFormal.IUT.N8Closure.C9HodgeSystemFromOriginal

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

noncomputable section

universe ua uv upi umon ui u v w

variable {l : PrimeGeFive} {V : Type uv}
  (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)

def sourceHodgeSystem : SourceHodgeTheaterBridge.SourceHodgeTheaterSystem l :=
  { source := I.initial
    source_universe_anchor := PUnit
    index := I.family.index
    theaterCarrier := HodgeTheater l V
    theater := I.family.theater
    distinct := I.family.distinct
    qParameter := fun i => (I.family.theater i).thetaPacket.q
    scale := fun i x => (I.family.theater i).thetaPacket.scale x
    link := fun i j t =>
      { arithmetic := t.arithmetic
        primeStrip := (I.family.link i j).primeStripEquiv t.primeStrip
        thetaPacket := t.thetaPacket }
    link_refl := by
      intro i t
      cases t
      rfl
    link_trans := by
      intro i j k t
      cases t
      rfl
    q_naturality := by
      intro i j
      exact I.family.link_q i j
    scale_naturality := by
      intro i j x
      exact I.family.link_scale i j x
    permutation := I.family.permutation
    permutation_q := by
      intro i
      exact I.family.permutation_q i
    permutation_scale := by
      intro i x
      exact I.family.permutation_scale i x }

#print axioms sourceHodgeSystem

end

end LeanFormal.IUT.N8Closure.C9HodgeSystemFromOriginal