# S951: ActualIndImageTransfer (corrected tensor packet types)

Date: 2026-10-30. Uses S940 actual image types; no fake endomorphism.

## Correct source carriers

* Ind1: S951Ind1Carrier j vQ P :=
    tensor product over Capsule j.val of DirectSumFactor at P.perm.symm i
    (reindexed packet; not an endomorphism of the source packet).
* Ind2: S951Ind2Carrier j vQ :=
    SourceProcessionCapsuleContract.tensorPacket Real C j vQ.
* Ind3: S951Ind3Carrier v m := ActualInd3Stage I v m.

## Exact minimal transfer

ActualIndImageTransfer (j vQ P f v m g) is a structure with:
* toBlock1/2/3 : source carrier -> qVFamTensorBlock T b;
* base1/2/3 : actual S940 base sets;
* image1/2/3 : Set (qVFamTensorBlock T b);
* image_i_eq : image_i = toBlock_i '' S940 image of base_i;
* ind1_actual/ind2_actual/ind3_actual : Prop.

No map is fabricated: all three toBlock maps are fields.  The images are
defined through the actual S940 image sets, not assumed.

ActualIndImageTransferRequired :=
  exists j vQ P f v m g, Nonempty (ActualIndImageTransfer ...).
No inhabitant is asserted.

## Construction into S928

actualIndImageDataOfTransfer X : S928.ActualIndImageData T b uses the actual
qVFam image sets X.image1/2/3 as source carriers and subtype projections as
maps.  actualIndImageDataOfTransfer_nonempty turns the exact transfer
obligation into S928 data.

This is the type correction requested: the transfer target is the qVFam block,
while the Ind1 carrier is the reindexed tensor packet, so no endomorphism is
used.
