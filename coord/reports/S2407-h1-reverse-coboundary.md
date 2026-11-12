# S2407: external coboundary to internal cohomology

Date: 2026-11-02. Layer O. Consumer: S2399 / S2384 / S2204.

## File

tmp/sheaf/xif/paper/S2407H1EquivActual.lean
Source SHA256 896ac190952479b02fdf9ccf93b8ecc786622f11f70b6bb38e31d45f51adc011
olean SHA256 1dfe90e81ef174fbc18b38efc69b1458c614e78006e8e99ff84ebab2abce6d41
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2407ExternalCoboundary_to_Cohomologous: if two internal continuous cocycles
c,d have external quotient c/d an external coboundary, then c and d are
internally Cohomologous.  The witness is x^{-1} for external witness x; the
algebra uses commutativity and act_g x^{-1} = (act_g x)^{-1}.

## Exact first missing

The quotient lift and equivalence:
  S2204H1 p n ≃ ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n).
S2399ToExternal is the actual forward map.  Remaining: define S2407ToInternal
by Quotient.lift on the external quotient, using
S2407ExternalCoboundary_to_Cohomologous for welldefinedness, then prove the two
composites are identities.  The relation-level reverse direction is now
actual; only the quotient lift/descent remains.

Once the equivalence exists, S2384FiniteH1OfComparison gives
Finite (S2204H1 p n).  No unconditional Finite or surjectivity is claimed.
