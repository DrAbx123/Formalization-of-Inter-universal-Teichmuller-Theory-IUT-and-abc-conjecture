# S1839: the S1828 universal slice filling is false (counterexample)

Date: 2026-11-01

Lean: tmp/sheaf/xif/paper/S1839SliceFillingActual.lean

EXIT=0

SHA256: D65A58A8739DBDC7770EA42AD75B2B6B7BA2DC588FD08548CB6F4573CA38C282

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1839SliceFillingActual.olean
(105632 bytes, SHA256 5ECB810BDC78500F084CA27AB6040442341634C3722814752CFED74341E34ED5)

Import check: the built olean was re-imported by a scratch module that re-printed
the main axiom sets; both the load and the checks succeeded.

## Result

S1828SliceFillsOver is refuted; it cannot be proved from the concrete
S1755/S1816/S1744 model-map constructions.

The concrete construction only proves the one-directional statement

  S1839ExtractionOverBase : every extraction value
    S1755ModelHomOfCoverMap A B f satisfies
    S1755ModelHomOfCoverMap A B f ≫ S1733ModelOver B = S1733ModelOver A

(restating S1812ModelHomOfCoverMap_triangle; equivalently the scheme-level
content of S1816ModelMap_over).  It does not prove that every model morphism is
an extraction value.

## Counterexample

* The terminal (identity) cover S1762TerminalCover of the actual S1726
  orbicurve has the chosen finite-etaleness S1762IdentityFiniteEtale, whose
  identity-point base-change presentation is the identity square.  Therefore

    S1839TerminalModel     : S1733Model S1762TerminalCover = S1726AffineOver   (rfl)
    S1839TerminalModelOver : S1733ModelOver S1762TerminalCover = 1              (rfl)

* At this pair, S1828SliceFillsOver reads: for every endomorphism g of Spec R'
  over Spec F', g ≫ 1 = 1, i.e. g = 1.

* But R' = F'[x,y]/(y^2 - x^3 - (61/64)x^2 + (125/64)x) has a non-identity
  F'-algebra endomorphism: the composite R' -> F' -> R' given by evaluation at
  the F'-point (0,0).  It sends x to 0, while x != 0 in R' (witnessed by the
  F'-point (1,0), which sends x to 1).  Hence g = Spec of this endomorphism is a
  non-identity endomorphism of Spec R' over Spec F'.

* S1839TerminalFilling_false: the filling triangle fails at this pair.
  S1839_not_sliceFillsOver:   not S1828SliceFillsOver.

## Consequences

* S1839NotExtractionImage: the constant endomorphism is not the extraction of
  any cover map.  Hence S1839_not_modelHomSurjective:
  not S1755ModelHomSurjective, and S1839_not_modelHomEquivMissing:
  not S1755ModelHomEquivMissing (both unconditional).

* With S1755SourceRetraction, S1828's dictionary S1828ModelHomEquivMissing_iff
  gives S1839_fillingConj_false:
  not (S1828SliceFillsOver and S1766CoverMapDiscrete).

* Therefore S1828R1ModelCategory has a refuted hypothesis.  R1 for
  S1733ModelCategory cannot be obtained from h = S1755SourceRetraction and
  hd = S1766CoverMapDiscrete through the filling.  The slice-corrected
  S1828R1 for S1828ModelOverCategory is unaffected.

## Axiom footprint

Only propext, Classical.choice and Quot.sound.  No sorry, no new axiom, no
Shrink/ULift/PUnit, no fake data.
