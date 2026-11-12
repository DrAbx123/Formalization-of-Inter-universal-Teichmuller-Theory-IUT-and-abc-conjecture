# LANA-PORT-PLAN — portable lana lemmas and the minimal port set

Status: READ-ONLY PLAN, 2026-11-12. No Lean file written, no compile run.
Authority: lana root tree Iut/ at this checkout; TG status from coord/TG-DRIFT-NOTES.md
and coord/LANA-PORT-LOG.md. The goal is the M = A - R expansion, the nonnegative
local terms, and the q-scaling normalization; NOT the whole lana paper.

## 0. Summary

Two disjoint layers exist in lana:

1. LocalConstruct / Cor312-container layer. Mostly Mathlib + number-field local
   arithmetic. It is portable if we replace the single import
   Iut.Cor312.Statement in Iut/Concrete/LocalTheory.lean and remove the
   ThetaLocalConstruct/Ordp / AdmissiblePrime upper imports. No TG package needed.
2. Wall / Concrete / ThetaData layer (Gap, VcI, Ind3, ThetaRegion, InitialThetaData,
   Anabelian, Literal, forms). It transitively imports TemperedFundamentalGroups.
   Those files are TG-drift-blocked (coord/TG-DRIFT-NOTES.md: NodeEtaleGlueReduced
   closure missing oleans, NilpotentFlatness RED). We cannot port them as-is.

The minimal plan therefore ports layer 1, then COPIES the small definitions/theorems
from layer 2 into our own Mzk1Ported* files with a minimal context record replacing
InitialThetaData. The copies are short definitions with local proofs, not imports of
TG files.

## 1. Requested lana items: source, dependency class, portability

Legend for dependency class:
- M = requires only Mathlib + earlier local definitions (portable independently).
- L = requires the LocalConstruct layer below it (portable after layer 1).
- C = source file is TG-blocked, but the declaration is a short definition/theorem;
  copy it into a ported file (copy-only, not import).
- T = truly TG-dependent (Anabelian/TemperedFundamentalGroups); do not port.

| requested item | lana source (file:line) | kind | class | port decision |
|---|---|---|---|---|
| componentVol_units_smul | Iut/Wall/IdentifiedCopies.lean:67 | theorem | C | copy into Mzk1PortedScaleVolumeActual.lean; proof uses only ScaleVolume/Volume |
| componentVol_prod_incl_smul_integral | Iut/Concrete/LocalConstruct/ScaleVolume.lean:118 | theorem | L | port file-for-file after LocalConstruct |
| hullPacket_finite | Iut/WallEquiv/VcI.lean:806 | theorem | C | copy; depends hullPacket/logShellRadius/shellExcess |
| hullPacket_tame | Iut/WallEquiv/VcI.lean:844 | theorem | C | copy; needs shellExcess_eq_tame (VcI:414) |
| defectPacket | Iut/WallEquiv/VcI.lean:703 | def | C | copy; shellDefect/archDefect definitions |
| defectPacket_nonneg | Iut/WallEquiv/VcI.lean:770 | lemma | C | copy |
| logVol_hull_vcI_eq | Iut/WallEquiv/VcI.lean:741 | theorem | C | copy; with ported packetVol/logVol |
| logVol_vcI_eq | Iut/WallEquiv/VcI.lean:736 | theorem | C | copy |
| gapHullAt | Iut/WallEquiv/Gap.lean:895 | def | C | copy only if the gap decomposition is needed; not minimal for M=A-R |
| ind2Term | Iut/WallEquiv/Gap.lean:747 | def | C | copy; thetaComponent/scaleElt/leastHull/shell |
| ind2Term_nonneg | Iut/WallEquiv/Gap.lean:756 | theorem | C | copy |
| packetVol | Iut/Cor312/LogVolume.lean:117 (field of LogVolumeData) | def | M | port Cor312 container/logvolume file-for-file |
| processionVol | Iut/Cor312/LogVolume.lean:207 | def | M | port |
| globalVol | Iut/Cor312/LogVolume.lean:177 | def | M | port |
| archDefect | Iut/WallEquiv/Gap.lean:459 | def | C | copy; depends LocalConstruct arch |
| archDefect_nonneg/pos | Iut/WallEquiv/Gap.lean:463/468 | theorem | C | copy |
| archLogShell | Iut/Concrete/LocalConstruct/ArchLogShell.lean:278 | def | L | port |
| archIntegral | Iut/Concrete/LocalConstruct/Archimedean.lean:328 | def | L | port |
| leastHull | Iut/WallEquiv/Gap.lean:87 | def | C | copy; only Tensor/integral/admissible |
| leastHull_eq/subset/smul_integral | Gap.lean:93/97/138 | lemmas | C | copy |
| logShellRadius | Iut/WallEquiv/VcI.lean:464 | def | C | copy; uses Iut.logShell/ordp |
| orderVol/shellExcess | Iut/WallEquiv/VcI.lean:93/158 | defs | C | copy; depends LocalConstruct tensorLogShell/order |
| componentVol | Iut/Concrete/LocalConstruct/Volume.lean:196 | def | L | port |
| haar/units scaling | Iut/Concrete/LocalConstruct/{Volume,ScaleVolume} | defs/lemmas | L | port |
| hullPacket/vcIPacket | Iut/WallEquiv/VcI.lean:689/683 | defs | C | copy; labels/tupleWeight/context |
| vcIComp/vcIAt/hullOf | Iut/Wall/Ind3.lean:58/80; Iut/Wall/Rss.lean:328 | defs | C | copy minimal definitions |
| logVol | Iut/Cor312/LogVolume.lean (logVol definition) | def | M | port |
| qroot/qOrder/scaleElt/thetaComponent | ThetaLocalConstruct/Data.lean:420; ThetaRegion.lean:126/136/170 | defs | T/C | dependency is TG; copy scaleElt/thetaComponent with a minimal context record, do not port Data.lean |

Note on componentVol_units_smul: C0 called it missing, but it is already present at
Iut/Wall/IdentifiedCopies.lean:67. Its file imports Iut.Wall.Checks, which pulls the
TG chain; therefore we copy the 14-line theorem into a portable ScaleVolume file
rather than importing IdentifiedCopies. The proof only uses
componentVol_units_smul_integral, haar_units_smul, and componentVol's definition.

## 2. TG-blocked imports (do not port)

Root package TemperedFundamentalGroups/:
- SemistableReduction/NodeEtaleGlueReduced.lean, NilpotentFlatness.lean,
  FormalPatchLevel.lean, and the 87-file closure: TG drift; RED/partial, missing
  oleans. See coord/TG-DRIFT-NOTES.md.
- Iut/Anabelian/Tempered.lean, Iut/Anabelian/GenuineEtale.lean,
  Iut/Anabelian/Genuine/*, Iut/Anabelian/Orbicurve: import TemperedFundamentalGroups.
- Iut/Cor312/ThetaData/Basic.lean and its closure (LocalConditions, Orbicurve,
  TateStructure, TateFamily, ...) transitively via GenuineEtale/Tempered.
- Iut/Concrete/ThetaRegion.lean, Iut/Concrete/ThetaLocalConstruct/Data.lean,
  EmbedCompletion.lean, TateCompat.lean, upper part of Ordp.lean:
  import ThetaData.Basic/AdmissiblePrime; TG-blocked.
- Iut/Concrete/Literal.lean, LocalEstimate.lean, Invariants.lean,
  Iut/WallEquiv/Basic.lean, Forms.lean, Gap.lean, VcI.lean,
  Iut/Wall/{Ind3,Rss,Pilots,EtaAlg,Checks,BPS}.lean, Iut/Cor312/Statement.lean,
  LeftHandSide.lean: TG-blocked via the above.
- Iut/Cor312/RightHandSide.lean imports ThetaData.Basic for InitialThetaData; the
  RHSData/rhs definitions are short and are copied, not imported.

Do not try to patch TG drift in this task. The existing record is
coord/TG-DRIFT-NOTES.md; C0 lana compilation is BLOCKED-BY-TG.

## 3. Portable layer 1: exact files

These files have no TG import once the two decouplings below are done:

Local arithmetic:
- Iut/Concrete/LocalTheory.lean (81 lines): imports only Iut.Cor312.Statement
  unnecessarily; all definitions use Mathlib NumberField. Replace the import with
  Mathlib and port as Mzk1PortedLocalTheoryActual.lean.
- Iut/Concrete/LocalConstruct/Packet.lean (657 lines): imports LocalTheory only;
  port after LocalTheory. Provides completionAt/Factor/Tensor/packetBasis.
- Iut/Concrete/ThetaLocalConstruct/Ordp.lean: lower part lines 41-124
  (under_int_eq ... ordp_nonneg_of_norm_le_one) is pure local field; port these
  facts as needed. Upper lines 156+ use EmbedCompletion/TateParameter and are not
  ported.
- Iut/Concrete/LocalConstruct/Arithmetic.lean (224 lines): replace the Ordp import
  with the ported local facts; port.

LocalConstruct volume/shell chain:
- Integral.lean (Packet), Indeterminacy.lean (Integral), MaximalOrder.lean
  (Indeterminacy), Haar.lean (Mathlib; already ported as
  Mzk1PortedLocalConstructActual.lean), Archimedean.lean (MaximalOrder; 401 lines),
  Volume.lean (MaximalOrder/Archimedean/Haar; 304 lines), TensorIntegral.lean
  (Volume/Arithmetic), ScaleVolume.lean (TensorIntegral; 153 lines),
  LocalLogShell.lean (PadicLogVolume.PadicLog; 114 lines), LogShell.lean
  (LocalLogShell/ThetaAdmissible/Arithmetic; ~420 lines), LogLattice.lean,
  FactorShell.lean, ArchLogShell.lean (ThetaAdmissible; 415 lines),
  Admissible.lean, ThetaAdmissible.lean, ArchIndAut.lean (ArchLogShell),
  IndAut.lean (LogShell/ArchIndAut).
- For shellExcess/logShellRadius/tame proofs: LocalDifferent.lean (Packet/
  Arithmetic/MaximalOrder/PadicLogVolume.TraceDuality; replace the Ordp import),
  Prop14Lattice.lean, ShellBound.lean, Prop14.lean, Hull.lean, ResidueField.lean.
  These are local field/lattice files; port only the subset needed by
  shellExcess_eq_tame and exists_isGreatest_logShellRadius.
- PadicLogVolume/PadicLog.lean and TraceDuality.lean are an external supporting
  package; check version drift separately; they are not TG.

Cor312 container/logvolume layer (all Mathlib-only or Container-local):
- Iut/Cor312/Procession.lean, RationalPlace.lean, PacketPresentation.lean,
  Container.lean (210 lines), HolomorphicHull.lean, ContainerHull.lean,
  LogVolume.lean (214 lines). Port file-for-file as
  Mzk1PortedContainerActual.lean / Mzk1PortedLogVolumeActual.lean.
- Iut/Cor312/RightHandSide.lean: do NOT port the file (imports ThetaData.Basic).
  Copy RHSData/rhs/thetaHull definitions into a generic RHSData with a minimal
  container/thetaPilot record; no InitialThetaData.

## 4. Copy-only layer 2: minimal pilot context

Create Mzk1PortedPilotContextActual.lean with a record containing only what the
volume/pilot definitions read (suggested fields):
  Kt : Type, [Field Kt], [NumberField Kt]
  Fmod : Type, [Field], [NumberField]
  ℓ : Nat, nC : Nat, hℓ / nC_eq
  qroot : FinitePlace Kt -> completionAt Kt w (or an abstract unit)
  qOrder : FinitePlace Fmod -> Nat and ordp_qroot law as a field/proof
  badChars : Set Nat, ramIdx, residueChar, localDeg
  labels : Type, distinguished : labels, tuple/tensor data
  qPilotSignedLogVolume : Real (the A-side scalar)
  weight : (rational place) -> ... -> Real, weight_pos proofs
This is a deliberate abstraction of InitialThetaData; it avoids importing
ThetaData.Basic/TG while preserving the exact definitions needed by
componentVol/logVol/hullPacket/defectPacket.

Copy definitions/theorems from:
- Iut/Wall/Ind3.lean:58/80 (vcIComp/vcIAt), Iut/Wall/Rss.lean:328 (hullOf).
- Iut/WallEquiv/Gap.lean:87 (leastHull), 459 (archDefect), 747 (ind2Term),
  895 (gapHullAt if needed).
- Iut/WallEquiv/VcI.lean:464 (logShellRadius), 93 (orderVol), 158 (shellExcess),
  683 (vcIPacket), 689 (hullPacket), 703 (defectPacket), 736/741 (logVol
  identities), 806/844 (hullPacket_finite/tame).
- Iut/Concrete/ThetaRegion.lean:126/136 (scaleElt/scaleEltAt), 170
  (thetaFiniteOn), 257 (thetaComponent), 261 (thetaFinite_eq).
- Iut/Wall/IdentifiedCopies.lean:67 (componentVol_units_smul).

These are copy-only. Do not import their source files (they import TG).

## 5. Minimal port set and dependency order

Phase 0 (already done): Haar port
  Mzk1PortedLocalConstructActual.lean.

Phase 1: Local arithmetic/packet (Mathlib-only)
  1. Mzk1PortedLocalTheoryActual.lean (LocalTheory.lean, ~100 lines)
  2. Mzk1PortedArithmeticActual.lean (Arithmetic.lean + lower Ordp facts, ~350 lines)
  3. Mzk1PortedPacketActual.lean (Packet.lean, ~700 lines)
  Depends: Mathlib/PadicLogVolume.

Phase 2: LocalConstruct volume/arch (portable)
  4. Mzk1PortedVolumeActual.lean (Integral/Indeterminacy/MaximalOrder/
     Archimedean/Volume/Haar; ~1200 lines)
  5. Mzk1PortedShellActual.lean (LocalLogShell/LogShell/LogLattice/FactorShell/
     ThetaAdmissible/Admissible; ~1200 lines)
  6. Mzk1PortedScaleVolumeActual.lean (TensorIntegral/ScaleVolume +
     componentVol_units_smul copy; ~300 lines)
  7. Mzk1PortedArchActual.lean (ArchLogShell/ArchIndAut/IndAut; ~900 lines)
  8. Mzk1PortedShellBoundActual.lean (LocalDifferent/Prop14Lattice/ShellBound/
     Prop14; only needed for shellExcess_eq_tame/logShellRadius; ~1000 lines)
  Estimate: 4.5-5k lines, 1.5-3 focused days; Mathlib only after phase 1.

Phase 3: container/logvolume (portable)
  9. Mzk1PortedContainerActual.lean (Procession/RationalPlace/
     PacketPresentation/Container; ~500 lines)
  10. Mzk1PortedLogVolumeActual.lean (HolomorphicHull/ContainerHull/LogVolume;
      ~450 lines)
  11. Mzk1PortedRHSActual.lean (RHSData/rhs/processionVol; ~250 lines)
  Estimate: ~1.2k lines, 0.5-1 day; no TG.

Phase 4: pilot copy layer (copy-only, TG-free)
  12. Mzk1PortedPilotContextActual.lean (~150 lines)
  13. Mzk1PortedPilotAlgebraActual.lean (vcIComp/hullOf/leastHull/
      scaleElt/thetaComponent; ~600 lines)
  14. Mzk1PortedPacketTermsActual.lean (vcIPacket/hullPacket/defectPacket/
      logVol identities; ~500 lines)
  15. Mzk1PortedInd2Actual.lean (ind2Term/ind2Term_nonneg; ~300 lines)
  16. Mzk1PortedArchDefectActual.lean (archDefect; ~100 lines)
  17. Mzk1PortedScalingActual.lean (sF/sum j^2/q-scaling normalization; already
      Mzk1ScalingNormalizationActual, no lana import)
  Estimate: ~1.7k lines, 1-2 days; depends only on phases 1-3.

Phase 5: final decomposition
  18. Mzk1PortedRExpansionActual.lean (packetVol(thetaHull) expansion;
      ~300 lines)
  19. Mzk1PortedMNonnegActual.lean (qPositiveSum + M=A-R; ~300 lines)
  Estimate: ~0.5 day after phases 3-4.

Total minimal port: about 8-9k lines of copied/ported local mathematics; calendar
estimate 3-5 focused days, dominated by phase 2 (LocalConstruct) and phase 3
(container). No TG module is ported.

## 6. Work estimates and risks

- Phase 1: low risk; LocalTheory 81 lines is only a Trivial import cleanup;
  Arithmetic needs the lower Ordp facts copied (lines 41-124), not the TG upper.
- Phase 2: medium risk. LogShell/ArchLogShell/ScaleVolume proofs are long but
  self-contained local field theory. The main adaptation risk is Mathlib Padic
  API drift (PadicLogVolume/PadicLog, TraceDuality), not TG.
- Phase 3: low risk; Cor312 container/logvolume are Mathlib-only.
- Phase 4: low mathematical risk but many copy edits. Minimal context must
  preserve exact definitions; do not replace with arbitrary fields.
- Phase 5: depends on the C0 exact lemmas (leastHull_thetaComponent_eq_pow_floor,
  archDefect_eq) for the nonnegative final form; port plan alone does not prove M>=0.
- TG modules not ported: no NilpotentFlatness, NodeEtaleGlueReduced, Anabelian/
  Tempered, GenuineEtale, ThetaData.Basic. If someone tries to import them the
  build will stay RED/MISSING; use copy-only files.

## 7. First step (concrete, no compile now)

Ticket P1: write Mzk1PortedLocalTheoryActual.lean by copying
Iut/Concrete/LocalTheory.lean and replacing
  import Iut.Cor312.Statement
with
  import Mathlib
(namespace rename to LeanFormal.IUT.XiFPaper.Mzk1PortedLocalTheoryActual,
attribution retained). This is the smallest TG-free root; it unlocks
Mzk1PortedPacketActual.lean. Hand to watchdog after writing; do not compile
manually.

Ticket P2 (parallel after P1): write Mzk1PortedContainerActual.lean by copying
Iut/Cor312/{Procession,RationalPlace,PacketPresentation,Container}.lean; these are
Mathlib-only and independent of the pilot chain.

Do not start phase 4 copies until phase 1-3 files have watchdog oleans; otherwise
the copy files will fail on missing imported definitions.
