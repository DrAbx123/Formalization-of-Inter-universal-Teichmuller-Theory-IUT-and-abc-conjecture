import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData

/-!
  # The q side of the Step-XI certificate: source-level comparison

  This module isolates the `q`-side comparison of the Corollary 3.12, Step (xi)
  certificate from the remaining data of the hull-volume interface.  The consumer
  slot is fixed by `CertificateHullWiring.lean`: `iqHullCertificate` takes
  `hq : ENNReal.ofReal q <= W.logVolume W.imageSet` together with `hqneg : q < 0`.
  For the source interface `sourceUnitRegionHaarInterface` the right-hand side is
  definitionally `I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)`
  (`sourceUnitRegionHaarInterface_image_logVolume_eq`).

  Findings, graded.

  * Proved (route 1, exact expression): the image-union log-volume is the supremum of
    `ENNReal.ofReal` of the signed normalized values `card * log (thetaValueAt n 0 j)`
    (`sourceSetVolume_possibleImage_eq_iSup_sourceQSide`), hence at least each term
    (`sourceSetVolume_possibleImage_ge_sourceQSide`).
  * Proved (route 2, normalized comparison transfer): every signed `q` with
    `q <= sourceQSideNormalizedValue n j0` satisfies the consumer-shaped ENNReal lower
    bound (`sourceSetVolume_possibleImage_ge_ofReal_of_sourceQSide_le`,
    `sourceUnitRegionHaarInterface_hqSlot_of_sourceQSide_le`).
  * Proved (route 3, sign isolation and encoding loss): the signed normalized value is
    negative exactly when the packet contraction `thetaValueAt < 1` holds
    (`sourceQSideNormalizedValue_neg_iff`); under that contraction at every label the
    image-union ENNReal log-volume is exactly `0`
    (`sourceSetVolume_possibleImage_eq_zero_of_forall_theta_lt_one`), so the consumer
    slot sees only `0 <= 0`.  The contraction is the named `q_contracting` input of
    `CertificateHullWiring.lean`, not derivable from `OriginalInput`
    (`thetaValueAt_pos` gives only positivity).
  * Proved (consumer-shape degeneracy): because `ENNReal.ofReal q = 0` for `q < 0`,
    the `hq` slot of `iqHullCertificate` is implied by `hqneg` alone for *any*
    interface realization (`iqHullCertificate_hqSlot_of_neg`).  The ENNReal slot
    therefore cannot express a signed q-side comparison; the real content is the
    real-valued statement above.

  Not proved here (gap, deliberately not assumed): a paper-faithful signed `q`
  carrier and the genuine comparison `q <= normalized theta log-volume` for the
  actual `q` of Corollary 3.12.  The conditional theorems take exactly that
  comparison as a named hypothesis; no equality of hull and image volumes, no
  LGP-link comparison, and no unproved theta evaluation is assumed.

  Boundary: this is a q-side comparison layer, not the I-layer construction; the
  `Psi^cns` carrier remains PARK.  The theta upper-bound slot of the consumer is a
  separate obstruction: under pointwise degree faithfulness the source hull volume
  is `top` (`sourceHullVolume_eq_top_of_degreeFaithful`), so no `h theta` slot is
  satisfiable for the source hull at this level of realization.

  Source correspondence: IUT III, Corollary 3.12, Step (xi); Remark 3.1.1, (ii).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u ua uv upi umon ui

/-- **Consumer-shape degeneracy of the `hq` slot (proved).**  `iqHullCertificate`
takes `hq : ENNReal.ofReal q <= W.logVolume W.imageSet` together with `hqneg : q < 0`.
For `q < 0` we have `ENNReal.ofReal q = 0`, so the `hq` slot holds for every interface
realization `W`; it carries no information beyond `hqneg`.  A signed q-side comparison
must therefore be stated in `Real` (see `sourceQSideNormalizedValue`). -/
theorem iqHullCertificate_hqSlot_of_neg {X : Type u}
    (W : IQHullLogVolumeInterface X) {q : Real} (hqneg : q < 0) :
    ENNReal.ofReal q <= W.logVolume W.imageSet := by
  rw [ENNReal.ofReal_of_nonpos hqneg.le]
  exact zero_le

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The signed real quantity of the q-side comparison at procession `n` and signed
label `j`: the index cardinality times the logarithm of the actual theta special
value, i.e. the procession-normalized theta log-volume of Remark 3.1.1, (ii).  This
is the value that a paper-faithful `q` must be compared with; the consumer's
`ENNReal.ofReal q` slot cannot see it (`iqHullCertificate_hqSlot_of_neg`). -/
def sourceQSideNormalizedValue (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) : Real :=
  (Fintype.card (SourceVolumeIndex l) : Real) *
    Real.log (I.thetaValueAt (n.val : Int) 0 j)

/-- **Route 1: exact expression.**  The log-volume of the union of possible
theta-pilot images is the supremum over the signed labels of `ENNReal.ofReal` of the
signed q-side values. -/
theorem sourceSetVolume_possibleImage_eq_iSup_sourceQSide (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) =
      iSup (fun j : SignedLabel l.value =>
        ENNReal.ofReal (I.sourceQSideNormalizedValue n j)) := by
  rw [I.sourceSetVolume_possibleImage_eq v R n hdeg]
  rfl

/-- **Route 1: single-label lower bound.**  Each signed q-side value, read in
`ENNReal`, is a lower bound for the image-union log-volume. -/
theorem sourceSetVolume_possibleImage_ge_sourceQSide (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (j0 : SignedLabel l.value) :
    ENNReal.ofReal (I.sourceQSideNormalizedValue n j0) <=
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  rw [I.sourceSetVolume_possibleImage_eq_iSup_sourceQSide v R n hdeg]
  exact le_iSup (fun j : SignedLabel l.value =>
    ENNReal.ofReal (I.sourceQSideNormalizedValue n j)) j0

/-- **Route 2: transfer of the signed comparison.**  If `q` is bounded by the signed
normalized theta value at one label, then `ENNReal.ofReal q` is bounded by the
image-union log-volume.  This is the exact mathematical comparison behind the
consumer's `hq` slot; for `q < 0` the conclusion is automatic
(`sourceSetVolume_possibleImage_hqSlot_of_neg`), so the signed hypothesis is the
substantive part. -/
theorem sourceSetVolume_possibleImage_ge_ofReal_of_sourceQSide_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (j0 : SignedLabel l.value) {q : Real}
    (hq : q <= I.sourceQSideNormalizedValue n j0) :
    ENNReal.ofReal q <=
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  le_trans (ENNReal.ofReal_le_ofReal hq)
    (I.sourceSetVolume_possibleImage_ge_sourceQSide v R n hdeg j0)

/-- **Route 3: sign isolation.**  The signed normalized value is negative exactly when
the theta special value is below one, i.e. exactly the packet contraction condition
`q_contracting` named in `CertificateHullWiring.lean`.  `OriginalInput` supplies only
`thetaValueAt_pos`, not this inequality. -/
theorem sourceQSideNormalizedValue_neg_iff (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    I.sourceQSideNormalizedValue n j < 0 <->
      I.thetaValueAt (n.val : Int) 0 j < 1 := by
  simpa only [sourceQSideNormalizedValue] using I.sourceThetaValue_neg_iff n j

/-- **Route 3: encoding loss under full contraction.**  If every theta special value
at procession `n` is below one (the packet contraction), then every signed normalized
value is negative, hence its `ENNReal.ofReal` is zero and the image-union log-volume
is exactly `0`.  The consumer's `hq` slot then sees only `0 <= 0`: the signed
comparison `q <= sourceQSideNormalizedValue n j` is invisible in `ENNReal`.  The
contraction `thetaValueAt < 1` is the named `q_contracting` input, not derivable from
`OriginalInput`. -/
theorem sourceSetVolume_possibleImage_eq_zero_of_forall_theta_lt_one (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (h : forall j : SignedLabel l.value,
      I.thetaValueAt (n.val : Int) 0 j < 1) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) = 0 := by
  rw [I.sourceSetVolume_possibleImage_eq_iSup_sourceQSide v R n hdeg]
  refine le_antisymm ?_ zero_le
  refine iSup_le fun j => ?_
  exact le_of_eq (ENNReal.ofReal_of_nonpos
    ((I.sourceQSideNormalizedValue_neg_iff n j).mpr (h j)).le)

/-- **Consumer bridge (definitional).**  For the source interface, the consumer's
`W.logVolume W.imageSet` is the source set log-volume of the possible theta-pilot
images.  The `hq` slot of `iqHullCertificate` is therefore exactly the left-hand side
of the source-level comparison theorems above. -/
theorem sourceUnitRegionHaarInterface_image_logVolume_eq (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).imageSet =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  rfl

/-- **Consumer-shaped conditional q slot.**  The signed comparison at one label
implies the `hq` slot of `iqHullCertificate` for the source interface.  Note: under
the degree-faithfulness hypothesis `hdeg` the datum `D` is uninhabited, because it
would make the source hull volume finite while
`sourceHullVolume_eq_top_of_degreeFaithful` makes it `top`; this theorem records the
interface shape, not a full certificate. -/
theorem sourceUnitRegionHaarInterface_hqSlot_of_sourceQSide_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (j0 : SignedLabel l.value) {q : Real}
    (hq : q <= I.sourceQSideNormalizedValue n j0) :
    ENNReal.ofReal q <=
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).imageSet := by
  rw [I.sourceUnitRegionHaarInterface_image_logVolume_eq v R n D]
  exact I.sourceSetVolume_possibleImage_ge_ofReal_of_sourceQSide_le
    v R n hdeg j0 hq

/-- **Unconditional consumer-shaped q slot.**  Every strictly negative `q` satisfies
the consumer's image-union lower bound at the source level, with no theta or degree
hypothesis.  Combined with `iqHullCertificate_hqSlot_of_neg`, this shows the `hq`
argument of `iqHullCertificate` is redundant given the `q < 0` field. -/
theorem sourceSetVolume_possibleImage_hqSlot_of_neg (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {q : Real}
    (hqneg : q < 0) :
    ENNReal.ofReal q <=
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  rw [ENNReal.ofReal_of_nonpos hqneg.le]
  exact zero_le

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT
