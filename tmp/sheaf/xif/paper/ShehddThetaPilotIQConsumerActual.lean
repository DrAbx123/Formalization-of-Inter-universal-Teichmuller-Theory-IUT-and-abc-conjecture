import LeanFormal.IUT.IUTII.Kummer.SourceThetaPilotIQContainment

/-!
# ShehddThetaPilotIQConsumerActual — one-place Theta-pilot IQ containment consumer

STEP 0 prior-art (reuse only; A475 search hit SourceThetaPilotIQContainment):
* possibleImage_subset_of_generator_mem (general orbit lemma);
* sourceLogShellOnePlaceFamily / SourceThetaPilotOnePlacePacket /
  sourceThetaPilotProductMap(_tprod) / sourceThetaPilotTensorIQPacket /
  sourceThetaPilotIQPacket;
* possibleImage_subset_sourceThetaPilotIQPacket and
  sourceThetaPilotProductMap_image_subset_tensorIQPacket.

This file exposes the containment consumers in one interface: a Theta-pilot generator in
the IQ packet forces the one-place possible image (and its product-map image) into the
tensor IQ packet; the pure-tensor product formula is restated for consumers.  No new
assumptions, no sorry/axiom; the full paper place tensor remains a tree/repo question
(the one-place reduction is exactly what this tree proves).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddThetaPilotIQConsumerActual

open LeanFormal.IUT

universe uK uM

/-- **PROVED consumer:** the one-place Theta-pilot possible image and its product-map
image are contained in the IQ packets whenever the generator is. -/
theorem thetaPilot_IQ_containment {l : PrimeGeFive} {G : LGPMonoid.{uM} l}
    {D : SourceLogShellDatum.{uK}} {j : Nat}
    {P : LGPMonoidAction G Rat (sourceLogShellOnePlaceFamily D j)}
    (T : ThetaPilotObject P ()) (hgen : T.generator ∈ sourceThetaPilotIQPacket D j) :
    T.possibleImage ⊆ sourceThetaPilotIQPacket D j ∧
      sourceThetaPilotProductMap D j '' T.possibleImage ⊆
        (sourceThetaPilotTensorIQPacket D j : Set D.K) :=
  ⟨possibleImage_subset_sourceThetaPilotIQPacket T hgen,
    sourceThetaPilotProductMap_image_subset_tensorIQPacket T hgen⟩

/-- **PROVED consumer:** the pure-tensor product formula of the one-place comparison map. -/
theorem thetaPilot_productMap_tprod (D : SourceLogShellDatum.{uK}) (j : Nat)
    (f : (i : Capsule j) → Unit → D.K) :
    sourceThetaPilotProductMap D j (PiTensorProduct.tprod Rat f) =
      ∏ i, f i () :=
  sourceThetaPilotProductMap_tprod D j f

/-- Row record: reused containment lemmas vs consumer interface. -/
def thetaPilotIQRows : List (String × String × String) :=
  [ ("general orbit containment lemma", "REUSED PROVED", "possibleImage_subset_of_generator_mem")
  , ("one-place family/packet/product map/tensor IQ packet", "REUSED DEF", "sourceLogShellOnePlaceFamily ... sourceThetaPilotIQPacket")
  , ("containment + product-map image containment", "COMPOSED PROVED", "thetaPilot_IQ_containment")
  , ("pure-tensor product formula", "REUSED PROVED", "sourceThetaPilotProductMap_tprod (consumer restatement)")
  , ("full paper place tensor (all places) source packet", "REPO-CURRENT-LIMIT", "tree proves the one-place reduction only (SourceThetaPilotIQContainment docstring)") ]

theorem thetaPilotIQRows_length : thetaPilotIQRows.length = 5 := rfl

#check thetaPilot_IQ_containment
#check thetaPilot_productMap_tprod
#check thetaPilotIQRows_length

end LeanFormal.IUT.XiFPaper.ShehddThetaPilotIQConsumerActual
end
