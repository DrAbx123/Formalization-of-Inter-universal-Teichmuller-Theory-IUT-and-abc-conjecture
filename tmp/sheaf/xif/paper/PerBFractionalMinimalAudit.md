# Minimal audit: per-b fractional construction vs actual normalized hull scalar

This audit checks the per-b fractional scalar prerequisites against the minimal
xi-f requirements. It records exactly which actual fields are present and which
are still missing. No missing item is replaced by a fake assumption.

## 1. What is actually present

### 1.1 Actual qVFamily coefficients
- qVFamTensorCoefficient is the actual qVFamily order.
- qVFamTensorCoefficient_pos is proved: the coefficient is strictly positive.
- qVFamTensorCoefficient_log_ne_zero is proved from c > 0 and p > 1.

### 1.2 Actual fractional scaled region inclusion
- qVFamLambdaOHull is qVFamQPilotRegion, the actual fractional-lattice scaled
  region with the qVFamily coefficient.
- qVFamThetaScaledRegion_subset_lambdaOHull proves, for every signed label with
  actual j^2 >= 1:
    qVFamThetaTensorRegion j subset qVFamLambdaOHull.
  This reuses the actual fractional-lattice antitone theorem.
- This is a containment of actual scaled regions. It is not yet a containment of
  actual image points.

### 1.3 Actual product image and hull
- qVFamilyThetaImagePoint and qVFamilyThetaProductImageSet are actual image
  points in the product value carrier.
- qVFamilyThetaHull is the actual holomorphic hull of that image set.
- qVFamilyThetaProductImage_subset_hull proves image set subset hull.
- This is on the product carrier, not on the per-b tensor block.

### 1.4 Actual Haar positivity/finiteness and ratio positivity
- qVFamCanonicalHaar_pos_lt_top proves the canonical unit-reference and canonical
  hull Haar measures are positive and finite.
- qVFamHaarRatio_pos proves the canonical hull/unit reference Haar ratio is
  positive.
- This is a positivity statement, not a nontriviality or log-nonzero statement.

### 1.5 Actual uniform-copy procession average
- qVFamUniformProcession is the finite signed-label uniform weight system with
  every value equal to qVFamLocalThetaHullLogVolume.
- qVFamUniformProcession_average proves average = local log.
- This equality is true because the copies are constructed identical. It does
  not by itself identify the local log with the paper procession normalization.

## 2. Minimal audit conditions and status

The minimal audit requires:

(A) actual theta-image points land in the actual lambda-O hull;
(B) the finite signed-label procession average equals the actual local
    normalized log-volume;
(C) the Haar ratio is positive finite and its log is nonzero for nontrivial
    scaling.

Status:

| condition | status |
|---|---|
| actual scaled regions subset lambda-O | present |
| actual image points subset lambda-O | missing |
| actual theta image point map into tensor block | missing |
| image set subset product hull | present, different carrier |
| average equals local log by identical copies | present |
| local log equals paper procession normalization | missing |
| Haar unit/hull positive finite | present |
| Haar ratio positive | present |
| Haar ratio finite and nonzero/log nonzero | finite for Real ratio, nonzero/log missing |
| coefficient c > 0 and coefficient log nonzero | present |
| actual lambda scaling element in tensor block | missing as a point/tensor, only coefficient region |

## 3. Missing actual fields

1. Tensor image alignment.
   qVFamilyThetaImagePoint is a product of real value-group points. The per-b
   fractional block qVFamTensorBlock is a p-adic completion tensor block. There
   is no actual field
     thetaImagePoint : SignedLabel -> qVFamTensorBlock
   with the property that it realizes qVFamilyThetaValue in the tensor block.
   The existing ThetaTensorQVFamAlignment only supplies coefficients, not image
   points.

2. Image-point landing.
   The actual theorem qVFamThetaScaledRegion_subset_lambdaOHull is a region
   inclusion. What is missing is
     thetaImagePoint j in qVFamLambdaOHull
   for each actual image point. A region inclusion does not imply point
   membership without the missing image alignment.

3. Actual tensor lambda element.
   The q-pilot scaled region is built from the fractional lattice coefficient
   c. The actual pure-tensor scaling element (the tensor of normalized qVFamily
   units in the selected completions) is not constructed as an element of
   qVFamTensorBlock. Only its coefficient is known.

4. Local Haar positivity/finiteness for the fractional hull.
   qVFamLocalThetaHullLogVolume uses Measure.addHaar on the local hull, but the
   actual theorem
     0 < Haar(qVFamLocalThetaHull) and Haar(...) < top
   is not supplied. The existing local inequality in
   GlobalQVFamThetaHullScalarActual is conditional on exactly these two facts.

5. Paper normalization equality.
   qVFamUniformProcession is uniform with identical local values. This proves
   the finite average equals that local value, but not that the local value is
   the paper procession-normalized mono-analytic log-volume. The exact missing
   comparison is the paper procession normalization comparison
     Haar(canonical hull) = thetaLogVolume / card(labels),
   or an equivalent average identity.

6. Product-hull normalization.
   qVFamThetaHullActual defines signedHullLogScalar only under
   HullLogDegreeBounded. The generic qVFamilyScalingUnits hull may have
   unbounded log-degree; a paper-faithful unit region/normalization is still
   missing. This is not a scalar prerequisite already satisfied.

7. Haar ratio nontriviality.
   qVFamHaarRatio_pos proves positivity. It does not prove
     qVFamHaarRatio != 1
   nor
     Real.log qVFamHaarRatio != 0.
   The coefficient-log nonzero theorem is a different scalar and cannot
   substitute for this ratio-log statement.

8. Carrier coherence.
   The per-b one-factor tensor block, the product value carrier of
   QVFamThetaHullActual, and the canonical tuple block are three actual
   carriers. The minimal scalar route may avoid a full transport, but it cannot
   claim the paper scalar without an actual normalization/coherence theorem
   relating the chosen local scalar to the paper procession average.

## 4. Verdict

The per-b fractional construction satisfies the minimal audit only at the
level of:

- actual scaled-region inclusion;
- actual coefficient positivity/log nonzero;
- actual canonical Haar positive finite and ratio positive;
- a formal identical-copy average.

It does **not** yet satisfy the full minimal audit for the paper normalized hull
scalar, because the actual image-point alignment, image-point landing, local
hull Haar positivity/finiteness, paper procession normalization equality, and
Haar-ratio log nontriviality are missing.

These are exact actual fields, not LGP/Kummer/Ind compatibility obligations.
Do not replace them by assumptions, a union hull, a constant tuple, or a
different scalar.
