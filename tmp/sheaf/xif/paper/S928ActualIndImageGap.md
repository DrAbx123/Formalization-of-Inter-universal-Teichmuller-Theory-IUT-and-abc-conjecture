# S928: actual Ind image exact gap (correction of S916 use)

Date: 2026-10-30. User correction: empty/theta-only S is only an internal lower
bound, NOT paper S; no final theorem may shrink paper S to theta-only.

## Status of S916

S916.paperSHull D with arbitrary/empty D is demoted to an internal lower bound.
The final paper S requires D = actual paper Ind image. S916's
modelHull_subset_paperSHull remains only a lower-bound containment, not a paper
result.

## Exact structure

ActualIndImageData:
* Ind1, Ind2, Ind3 : Type;
* toBlock1/2/3 : source -> qVFamTensorBlock T b;
* image1/2/3 : Set (qVFamTensorBlock T b);
* image1_eq_range etc: image_i = range toBlock_i;
* ind1_actual/ind2_actual/ind3_actual : Prop.

actualIndImage D := image1 union image2 union image3.
actualPaperS D := closure (paperRootThetaImageNZ union actualIndImage D).

This is the only paper-faithful S shape; no empty/default image is used.

## Exact gap

S928ActualPaperSRequired := Nonempty (ActualIndImageData T b).
No inhabitant is asserted. The actual Ind1/Ind2/Ind3 transfer data is missing.

## Internal lower bound only

S928ThetaOnlyLowerBound is rfl (theta subset theta) and
thetaLowerBound_subset_actualPaperS D holds for any actual D. Neither is a final
paper S theorem.

No target changed; no trivialization; no equality/scaling data.
