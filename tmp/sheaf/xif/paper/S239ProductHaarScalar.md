# S239: exact obstruction for product Haar scalar comparison

Date: 2026-10-29. Object-first; no inequality.

## Obstruction

The S227 transported tensor Haar tensorHaarTransport is a Measure for the
transported MeasurableSpace tensorBlockMeasurableSpace (a map of the L Borel
space under the inverse linear equivalence).

The independent blockHaar (RootTensorHaarTransportActual) is a Measure for the
norm-Borel MeasurableSpace of rootTensorBlock.

These are different types, so equality/scalar comparison of the two measures
cannot be stated directly, and Haar uniqueness cannot be applied without a
common measurable/Haar API on the tensor block.  In particular the pushforward
blockHaar-to-L map (which would make Haar uniqueness applicable) needs a
continuous linear equivalence, while S214/S227 only provide the linear
equivalence.

## Recorded exact requirement

ProductHaarScalarGap records the tensor measurable space, the block measurable
space, and the common Haar/measure comparison proposition.

ProductHaarScalarGapRequired is its nonemptiness; no inhabitant/equality/scalar
is asserted.

No fake Haar/scalar/sorry/axiom/True/PUnit; no inequality.
