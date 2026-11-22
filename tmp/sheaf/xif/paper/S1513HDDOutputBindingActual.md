# S1513: output-dependent rank-2 O_v-lattice binding to source.image

Date: 2026-10-31. Lean file: tmp/sheaf/xif/paper/S1513HDDOutputBindingActual.lean.
EXIT=0; olean generated.

## What is constructed

Given an actual S1402 source D and the missing integral image generator family
G : S1513ImageGeneratorFamily D, the file constructs the output-dependent
rank-2 O_v-lattice family

  s1513DiagonalLattice G o v = range (diag (G.gen o v 0 v) (G.gen o v 1 v))

and proves, for every output o and place v:

* Module.Free, Module.Finite, Module.finrank = 2;
* every lattice vector is integral over O_v;
* the K_v-span of the lattice is top;
* the lattice is exactly the O_v-span of the two generator vectors
  (s1513DiagonalLattice_eq_span);
* each generator vector is the actual image value in its coordinate.

S1513HDDOutputBinding.toS1500 packages this as an inhabitant of the S1500
target S1500OutputDependentHDDLattice, including imageGenerator_mem.  This is
a conditional constructor: neither the S1402 source nor the generator family
is constructed here.

## Precise first missing binding

S1513ImageGeneratorFamily D: two output/place-indexed points of D.image whose
values at the selected place are integral and nonzero.  The S1402 source fields
do not imply this:
* s1513SingletonSource_no_generator: a singleton image at a point with a
  non-integral coordinate admits no integral generator family;
* s1513ExistsNonintegralElement: every actual place has a non-integral
  element (inverse of a uniformizer).

The S1500 target as stated is strictly weaker: for every source D,
s1513OutputIndependentWitness D inhabits it with the output-independent S1476
lattice (s1513S1500Target_does_not_force_output_dependence).  Thus the S1500
imageGenerator_mem field alone does not force actual binding; the generator
family above is the first genuine missing binding.  This output-independent
witness is documented as an under-specification witness, not as the paper
object.

## No fake

No sorry, axiom, True, PUnit, rank-one surrogate or constant image is used as
the paper object.  The output-independent S1476 lattice appears only in the
documented under-specification witness.  Axioms of the key declarations are
only propext, Classical.choice, Quot.sound.

## Verification

Command:
  lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1513HDDOutputBindingActual.olean tmp/sheaf/xif/paper/S1513HDDOutputBindingActual.lean
EXIT=0.

Source SHA256: 711DA849C5E2B612D2D7608AC466C280E52F141BEE87D26CC89CD8673BA09D4E
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1513HDDOutputBindingActual.olean
Olean size: 801984 bytes
Olean SHA256: C900B829F85189592286699FD75FFBD245FD99190965253BBC6BE5B0EC47C505
