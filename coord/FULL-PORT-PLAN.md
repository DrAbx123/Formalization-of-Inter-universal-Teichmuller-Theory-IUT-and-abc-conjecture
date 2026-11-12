# FULL-PORT-PLAN — LocalTheory/ThetaRegion/ThetaLocalConstruct complete import closure

Status: READ-ONLY closure analysis, 2026-11-12. No compile, no Lean file.
Roots:
  Iut/Concrete/LocalTheory.lean
  Iut/Concrete/ThetaRegion.lean
  Iut/Concrete/ThetaLocalConstruct/{Data,EmbedCompletion,Ordp,Roots,TateCompat}.lean
Plus all other files under Iut/Concrete/ThetaLocalConstruct (five files; same set).

All imported Iut modules resolved transitively from the workspace source tree.
External imports are listed separately; no Iut source file is missing.

## 1. Closure summary

- 101 Iut source files in the closure.
- 70 external import modules:
  - Mathlib: 28
  - TemperedFundamentalGroups: 32
  - Pi1: 6
  - TateCurvesTheta: 2
  - PadicLogVolume: 2
- External source availability:
  - All 101 Iut files exist in tmp/external/ported/lana/Iut/... (101/101).
  - 11 files are byte-identical to external lana source.
  - 90 files differ from external lana source and must be audited/adapted when
    ported; all seven root files are among the 90 differences.
  - External dependency source directories exist: Mathlib, TateCurvesTheta, Pi1,
    TemperedFundamentalGroups, PadicLogVolume. Sampled oleans exist, but the
    external dependency closure was not rebuilt in this audit; the 15
    TemperedFundamentalGroups.SemistableReduction modules are known RED-risk
    and must be validated by the watchdog before the port batches that need them.
- Iut is already a lean_lib in lakefile.toml, so porting means compiling the
  actual Iut target files, not creating a new package.

## 2. Byte-identical external files (low-risk reuse)

Iut/Concrete/LocalConstruct/Haar.lean
Iut/Concrete/LocalConstruct/LocalLogShell.lean
Iut/Cor312/PacketPresentation.lean
Iut/Cor312/Procession.lean
Iut/Cor312/RationalPlace.lean
Iut/Cor312/ThetaData/Places.lean
Iut/Cor312/ThetaData/PointMap.lean
Iut/Cor312/ThetaData/UltrametricSqrt.lean
Iut/Torsion/Identities.lean
Iut/Tower/IntegralModel.lean
Iut/Tower/ReductionKernel.lean

All other 90 closure files differ from external lana; use diff/adapt, not blind copy.
The seven roots themselves all differ.

## 3. Full closure by dependency layer

Layer 0 (11):
Iut/Concrete/LocalConstruct/Haar.lean
Iut/Concrete/LocalConstruct/LocalLogShell.lean
Iut/Cor312/PacketPresentation.lean
Iut/Cor312/Procession.lean
Iut/Cor312/RationalPlace.lean
Iut/Cor312/ThetaData/Places.lean
Iut/Cor312/ThetaData/PointMap.lean
Iut/Cor312/ThetaData/UltrametricSqrt.lean
Iut/Torsion/Identities.lean
Iut/Tower/IntegralModel.lean
Iut/Tower/ReductionKernel.lean

Layer 1 (11):
Iut/Anabelian/Genuine/Basic.lean
Iut/Anabelian/Model.lean
Iut/Concrete/LocalConstruct/LogLattice.lean
Iut/Cor312/Container.lean
Iut/Cor312/HolomorphicHull.lean
Iut/Cor312/ThetaData/GlobalField.lean
Iut/Cor312/ThetaData/PlacesOver.lean
Iut/Cor312/ThetaData/TateIsomorphism.lean
Iut/Cor312/ThetaData/TateStructure.lean
Iut/Cor312/ThetaData/VariableChangePoint.lean
Iut/Torsion/EDS.lean

Layer 2 (9):
Iut/Anabelian/Local.lean
Iut/Anabelian/TateTorsion.lean
Iut/Cor312/ContainerHull.lean
Iut/Cor312/LogVolume.lean
Iut/Cor312/ThetaData/AdmissiblePrime.lean
Iut/Cor312/ThetaData/QuadraticExtension.lean
Iut/Cor312/ThetaData/TateStructureOfIso.lean
Iut/Torsion/Count.lean
Iut/Tower/IntegralTorsion.lean

Layer 3 (7):
Iut/Concrete/ThetaLocalConstruct/Roots.lean
Iut/Cor312/ThetaData/ReductionNorm.lean
Iut/Cor312/ThetaData/TateFamily.lean
Iut/Cor312/ThetaData/TateStructureTransport.lean
Iut/Cor312/ThetaData/TateStructureUnique.lean
Iut/Cor312/ThetaData/TwoTorsion.lean
Iut/Torsion/Divisible.lean

Layer 4 (5):
Iut/Anabelian/Genuine/Pi1.lean
Iut/Cor312/ThetaData/BadPlaceNorm.lean
Iut/Cor312/ThetaData/GalCompletion.lean
Iut/Cor312/ThetaData/PlaceUnder.lean
Iut/Cor312/ThetaData/ValuationTransfer.lean

Layer 5 (5):
Iut/Anabelian/Genuine/Inertia.lean
Iut/Anabelian/Genuine/Orbifold.lean
Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean
Iut/Cor312/ThetaData/TateFamilyGalois.lean
Iut/Cor312/ThetaData/TateParameterAt.lean

Layer 6 (5):
Iut/Anabelian/Genuine/Cover.lean
Iut/Concrete/ThetaLocalConstruct/TateCompat.lean
Iut/Cor312/ThetaData/LocalAut.lean
Iut/Cor312/ThetaData/TateFamilyOfSplit.lean
Iut/Cor312/ThetaData/TateSign.lean

Layer 7 (3):
Iut/Anabelian/Genuine/Realize.lean
Iut/Anabelian/Genuine/Theory.lean
Iut/Cor312/ThetaData/SqrtAtBadPlace.lean

Layer 8 (3):
Iut/Anabelian/Genuine/Homs.lean
Iut/Anabelian/Tempered.lean
Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean

Layer 9 (1):
Iut/Anabelian/Genuine/Core.lean

Layer 10 (1):
Iut/Anabelian/Genuine/Punctured.lean

Layer 11 (1):
Iut/Anabelian/GenuineEtale.lean

Layer 12 (1):
Iut/Cor312/ThetaData/Orbicurve.lean

Layer 13 (1):
Iut/Cor312/ThetaData/LocalConditions.lean

Layer 14 (1):
Iut/Anabelian/Torsion.lean

Layer 15 (2):
Iut/Anabelian/LocalInputs.lean
Iut/Cor312/ThetaData/LocalTateOfExistence.lean

Layer 16 (1):
Iut/Cor312/ThetaData/Basic.lean

Layer 17 (2):
Iut/Cor312/LeftHandSide.lean
Iut/Cor312/RightHandSide.lean

Layer 18 (1):
Iut/Cor312/Statement.lean

Layer 19 (1):
Iut/Concrete/LocalTheory.lean

Layer 20 (2):
Iut/Concrete/LocalConstruct/Packet.lean
Iut/Concrete/ThetaLocalConstruct/Ordp.lean

Layer 21 (2):
Iut/Concrete/LocalConstruct/Arithmetic.lean
Iut/Concrete/LocalConstruct/Integral.lean

Layer 22 (1):
Iut/Concrete/LocalConstruct/Indeterminacy.lean

Layer 23 (1):
Iut/Concrete/LocalConstruct/MaximalOrder.lean

Layer 24 (3):
Iut/Concrete/LocalConstruct/Archimedean.lean
Iut/Concrete/LocalConstruct/LocalDifferent.lean
Iut/Concrete/LocalConstruct/ResidueField.lean

Layer 25 (2):
Iut/Concrete/LocalConstruct/PacketDifferent.lean
Iut/Concrete/LocalConstruct/Volume.lean

Layer 26 (3):
Iut/Concrete/LocalConstruct/Admissible.lean
Iut/Concrete/LocalConstruct/Prop14.lean
Iut/Concrete/LocalConstruct/TensorIntegral.lean

Layer 27 (3):
Iut/Concrete/LocalConstruct/Hull.lean
Iut/Concrete/LocalConstruct/ScaleVolume.lean
Iut/Concrete/LocalConstruct/ThetaAdmissible.lean

Layer 28 (2):
Iut/Concrete/LocalConstruct/ArchLogShell.lean
Iut/Concrete/LocalConstruct/LogShell.lean

Layer 29 (2):
Iut/Concrete/LocalConstruct/ArchIndAut.lean
Iut/Concrete/LocalConstruct/FactorShell.lean

Layer 30 (2):
Iut/Concrete/LocalConstruct/IndAut.lean
Iut/Concrete/LocalConstruct/LatticeSandwich.lean

Layer 31 (1):
Iut/Concrete/LocalConstruct/Prop14Lattice.lean

Layer 32 (1):
Iut/Concrete/LocalConstruct/ShellBound.lean

Layer 33 (1):
Iut/Concrete/LocalConstruct/Theory.lean

Layer 34 (1):
Iut/Concrete/Container.lean

Layer 35 (1):
Iut/Concrete/ThetaLocalConstruct/Data.lean

Layer 36 (1):
Iut/Concrete/ThetaRegion.lean

## 4. Six port batches (strict layer ranges, no cross-batch import edges)

Batch P1 (layers 0-1, 22 files): foundation arithmetic/Haar/Cor312 packet basics.
  Order: layer 0 (11) then layer 1 (11).
Batch P2 (layers 2-4, 21 files): Cor312 LogVolume/ThetaData base, Anabelian local,
  Torsion Count/EDS/Divisible.
  Order: layer 2 (9) -> layer 3 (7) -> layer 4 (5).
Batch P3 (layers 5-8, 16 files): ThetaLocalConstruct EmbedCompletion/TateCompat,
  Tate family/galois, Anabelian Genuine inertia/cover/realize/theory/homs.
  Order: layer 5 (5) -> 6 (5) -> 7 (3) -> 8 (3).
Batch P4 (layers 9-15, 8 files): Anabelian Genuine core/punctured/etale/torsion,
  Cor312 orbicurve/local conditions, LocalInputs/LocalTateOfExistence.
  Order: layer 9 (1) -> ... -> layer 15 (2).
Batch P5 (layers 16-24, 14 files): Cor312 Basic/Left/Right/Statement, LocalTheory,
  LocalConstruct Packet/Ordp/Arithmetic/Integral/Indeterminacy/MaximalOrder/
  Archimedean/LocalDifferent/ResidueField.
  Order: layer 16 (1) -> ... -> layer 24 (3).
Batch P6 (layers 25-36, 20 files): LocalConstruct PacketDifferent/Volume/Admissible/
  Prop14/TensorIntegral/Hull/ScaleVolume/ThetaAdmissible/ArchLogShell/LogShell/
  ArchIndAut/FactorShell/IndAut/LatticeSandwich/Prop14Lattice/ShellBound/Theory,
  Iut/Concrete/Container, ThetaLocalConstruct/Data, ThetaRegion.
  Order: layer 25 (2) -> ... -> layer 36 (1).

Totals: 22+21+16+8+14+20 = 101 files.
By construction every import of a file in batch Pk is in an earlier or the same
layer; same-batch edges are strictly layer-ascending, so the listed inner order
is a valid watchdog order. No batch needs a file from a later batch.

## 5. External dependency caveat

The 101 Iut files themselves are source-complete externally. The external
imports are:
- Mathlib (28): same toolchain mathlib v4.32.2; no port work expected.
- TemperedFundamentalGroups (32): source dir present, but 15 modules are under
  SemistableReduction, the known RED/blocked area in prior audits. These must be
  validated first; if any is RED, P3/P4 and possibly P6 are blocked at import.
- Pi1 (6): source dir present; sample olean exists.
- TateCurvesTheta (2): source dir present; sample olean exists.
- PadicLogVolume (2): source dir present; sample olean exists.

Therefore:
- No closure file requires writing from scratch: external lana source has all 101.
- 11 files can be reused byte-identically.
- 90 files (including all seven roots) require diff/adapt because our working
  Iut source differs from external lana; do not blind-copy.
- The true external gating risk is the TemperedFundamentalGroups.SemistableReduction
  import set, not the 101 Iut files themselves.

## 6. Watchdog sequence recommendation

P1 -> P2 -> P3 -> P4 -> P5 -> P6, with inner layer order as listed. Before P3,
build/check the external TemperedFundamentalGroups semistable modules. Before P5,
check Cor312.Statement/LocalTheory. Before P6, check all LocalConstruct leaves.
No manual compile in this plan; hand P1 file list to watchdog after validation.
