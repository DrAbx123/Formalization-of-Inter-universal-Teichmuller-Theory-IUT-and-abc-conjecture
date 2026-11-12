# S2050 local CFT port: Reciprocity.Artin green

Date: 2026-11-02. Layer O; consumer S2039 M2a/M2b / S2027.

## P0 source

Copied external LANA sources to

  D:/lean/tmp/local-cft-port/local-class-field-theory-main
  D:/lean/tmp/local-cft-port/continuous-kummer-theory-main

External: Lean 4.32.0, Mathlib 81a5d; project: Lean 4.32.2, Mathlib 905b.

## CK (P1) status

All 19 ContinuousKummerTheory modules compiled, including Kummer.PAdic,
Zhat, ProfiniteCompletion, Topology, Values, Specialization, Decomposition,
root.  EXIT=0; root olean 3400 B.  (Prior S2054 audit.)

## PadicField status

19/19 compiled (S2053 audit), EXIT=0.

## Reciprocity port (this package)

Compiled EXIT=0:

- Reciprocity.LevelNeukirch (needs maxHeartbeats=2e6);
- Reciprocity.Embedding;
- Reciprocity.CyclicRec;
- Reciprocity.FrobLiftPow;
- Reciprocity.Abelian;
- Reciprocity.Artin;
- Reciprocity.ArtinContinuous;
- Reciprocity.BaseChange;
- Reciprocity.Existence;
- Reciprocity.Kummer;
- Reciprocity.NormCompat;
- Reciprocity.Conjugation;
- Reciprocity.NormLimitation;
- Reciprocity.ExistenceTheorem;
- Reciprocity.ArtinInertia;
- Reciprocity.ArtinUnique.

Artin file:

  source  tmp/local-cft-port/Reciprocity/Artin.lean
  SHA256  5CEBB80D88C2406294258DFF5F5FBD379B7DF96CBB144E50034E102B0A5B44E6
  olean   .lake/build/lib/lean/Reciprocity/Artin.olean
  olean SHA 0050D423455CDF5115BA4059D9F53CB2D433B43FAB0A066E3D4DBE2193AFB8C5
  size 1025192

Axiom probes:

  PadicField.artin                 : propext, Classical.choice, Quot.sound
  PadicField.artin_apply_eq_self_iff: trio
  PadicField.mem_ker_artin_iff      : trio
  PadicField.mem_absInertia_of_artin: trio

PadicField.artin type:

  K^x ->* Gal(maxAbelian K Omega / K)

## Exact first missing for S2027 M2a

The port gives LANA's maximal abelian extension maxAbelian K Omega, while
S2027 uses

  maximalAbelianExtension p U = fixedField (closure [Gal(Qbar_p/L), Gal(...)])

and Gal(L^ab/L).  The exact first missing bridge is the equality

  maxAbelian (localField p U) (AlgebraicClosure Q_p)
    = maximalAbelianExtension p U

or an equivalence of the two intermediate fields, plus the induced

  Gal(maxAbelian / L) ~= Gal(maximalAbelianExtension / L).

Only after that can PadicField.artin be typed as

  (localField p U)^x ->* Gal(L^ab/L)

and restricted to unitProfiniteCompletion to give M2a-core.

Second missing: artin injection/surjectivity on torsion (ArtinInertia has
artin_injective for finite abelian levels; global Artin map injectivity/existence
is in ExistenceTheorem/ArtinUnique, but the maxAbelian identification is the
type-level first field).

## M2b/Brauer.ArtinTransfer

Brauer directory was not copied in P0 (the port only copied PadicField, Galois,
Herbrand, ClassFieldAxiom, Reciprocity).  Brauer.ArtinTransfer needs the Brauer
closure (Absolute, ArtinPairing, CorBr, ContH2, ...), which is not yet ported.
Exact first action: copy/adapt LocalClassFieldTheory/Brauer/* and compile in
topological order; then apply artin_transfer.

## Conclusion

- BUILT: CK 19/19; PadicField 19/19; Reciprocity.Artin and 15 Reciprocity
  modules EXIT=0; artin axioms trio.
- MISSING first M2a bridge: maxAbelian = maximalAbelianExtension (or field
  equivalence) and induced Galois-group equivalence.
- MISSING M2b: Brauer closure / ArtinTransfer not copied yet.
- no fake/axiom; no LocalArtinSourceData inhabitant assumed.
