# S916: paper multiradial S, containment only

Date: 2026-10-30. Adjusted to the user's inequality-only instruction: no
equality, no hull-log formula, no scaling data.

## S

PaperIndImageData records:
* indImage : Set (qVFamTensorBlock T b);
* ind1_transfer/ind2_transfer/ind3_transfer : Prop;
no image equality is asserted.

paperSImageUnion D := paperRootThetaImageNZ union D.indImage.
paperSHull D := closure (paperSImageUnion D).

## Actual containment

modelHull_subset_paperSHull (D):
  modelHull T b subset paperSHull T b D.

Proof uses only the theta image part: modelHull = least lambda-O hull, the
one-label theta region equals the lambda-O cRoot region, hence modelHull is
inside the theta image union and its closure. No equality S = lambda.

modelHull_ssubset_paperSHull_of_strict:
  PaperSStrictEnlargement D -> modelHull T b ⊂ paperSHull T b D,
where PaperSStrictEnlargement D := exists x in D.indImage outside modelHull.

## Exact Ind data

PaperIndImageTransferRequired D := D.ind1_transfer and D.ind2_transfer and
D.ind3_transfer.  The Ind1/Ind2/Ind3 actions on tensor packets/x-mu stages
have no supplied transfer into the qVFam tensor block; the image set and the
three transfer Props are the exact structure.  No fake Ind image.

Only containment/proper containment is proved; no equality, no log formula.
