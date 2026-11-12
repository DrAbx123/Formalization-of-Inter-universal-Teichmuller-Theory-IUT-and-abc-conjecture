# LANA-PORT-TARGETS-V2 — script handoff for lana Phase 1-3 + copy-only manifest

Status: READ-ONLY HANDOFF, 2026-11-12. No file ported, no compile run.
Script: tools/xif_external_port.ps1 (only -Analyze / -Port used here; -Compile is
left to mainline/watchdog because manual compile is forbidden).

## 0. Script contract

The script -SrcRoot is the module root; -Targets are file paths relative to it;
-PortRoot/<Name> is the output root; internal imports are rewritten to
tmp.external.ported.<Name>.<module>. It performs Analyze (import closure, missing
Mathlib/prereqs) or Port (copy closure, attribution header, import rewrite,
optional rule patching). It does NOT classify TG; therefore choose targets/staging
that exclude TG.

Handoff commands (placeholder paths; mainline to run, not stepxi). Use one line:

  tools/xif_external_port.ps1 -Name lana-container -SrcRoot D:/lean -PortRoot D:/lean/tmp/external/ported -Targets 'Iut/Cor312/LogVolume.lean;Iut/Cor312/ContainerHull.lean' -Analyze

  tools/xif_external_port.ps1 -Name lana-container -SrcRoot D:/lean -PortRoot D:/lean/tmp/external/ported -Targets 'Iut/Cor312/LogVolume.lean;Iut/Cor312/ContainerHull.lean' -Port

  tools/xif_external_port.ps1 -Name lana-core -SrcRoot D:/lean/tmp/lana-port-src -PortRoot D:/lean/tmp/external/ported -Targets 'Iut/Concrete/LocalConstruct/ScaleVolume.lean;Iut/Concrete/LocalConstruct/ArchLogShell.lean;Iut/Concrete/LocalConstruct/IndAut.lean;Iut/Concrete/LocalConstruct/ShellBound.lean' -Analyze

Then the same with -Port. Do NOT pass -Compile; watchdog consumes the ported files.

## 1. Batch A: direct script port (no staging, no TG in closure)

These Cor312 files have imports only Mathlib or each other; closure is TG-free:

  A1 Iut/Cor312/Procession.lean
  A2 Iut/Cor312/RationalPlace.lean
  A3 Iut/Cor312/PacketPresentation.lean
  A4 Iut/Cor312/Container.lean
  A5 Iut/Cor312/HolomorphicHull.lean
  A6 Iut/Cor312/ContainerHull.lean
  A7 Iut/Cor312/LogVolume.lean
  A8 PadicLogVolume/PadicLog.lean (only if LocalLogShell is in Phase 2 target)
  A9 PadicLogVolume/TraceDuality.lean (only if LocalDifferent is in Phase 2 target)

Direct target order: A1, A2, A3, A4, A5, A6, A7, then A8/A9 if required.
RightHandSide.lean is NOT a direct target (it imports Iut/Cor312/ThetaData/Basic,
which is TG-blocked). RHSData/rhs are copied in Phase 4, not ported here.

Expected closure for A7: Procession/RationalPlace/PacketPresentation/Container
plus LogVolume; file count about 5-6, all Mathlib-only. If -Analyze reports
ThetaData/Anabelian/TemperedFundamentalGroups in the closure, stop and report:
a new import was added and the direct batch is no longer safe.

## 2. Batch B: staged + directed decoupling (Phase 1-2 LocalConstruct)

The raw LocalConstruct closure is NOT directly portable because:
  - Iut/Concrete/LocalTheory.lean imports Iut/Cor312.Statement at line 6;
  - Iut/Concrete/LocalConstruct/Arithmetic.lean and LocalDifferent.lean import
    Iut/Concrete/ThetaLocalConstruct/Ordp.lean, whose upper part imports
    EmbedCompletion / ThetaData.AdmissiblePrime (TG chain).

Make a staging source root (copy only, no compile):

  tmp/lana-port-src/

with the Iut/Concrete tree and the required PadicLogVolume files. Apply exactly
two directed decouplings:

D1. Iut/Concrete/LocalTheory.lean
    - replace line 6:  import Iut.Cor312.Statement
    + replace with:    import Mathlib
    All definitions in that file use Mathlib NumberField only; no Statement symbol
    is used in the body. Keep namespace/copyright.

D2. Iut/Concrete/ThetaLocalConstruct/Ordp.lean
    Create a minimal staged Ordp file containing only the local lower block
    needed by Arithmetic/LocalDifferent:
      imports: Mathlib + Iut.Concrete.LocalTheory
      lines 41-124 of source: under_int_eq, under_int_ne_bot, under_int_isMaximal,
      liesOver_span_residueChar, absNorm_eq_pow_residueChar, inertDeg_pos',
      ramIdx_pos', norm_eq_zpow_of_valued, ordp_eq_of_valued, ordp_pow',
      ordp_nonneg_of_norm_le_one.
    Drop imports Iut.Concrete.ThetaLocalConstruct.EmbedCompletion and
    Iut.Cor312.ThetaData.AdmissiblePrime, and drop the upper block 156+ that uses
    EmbedCompletion/TateParameter. Arithmetic/LocalDifferent do not reference the
    dropped names (checked by rg: only ordp_/ramIdx_/inertDeg_ lower facts are used).

After D1/D2 the script may target these leaf roots; the script topo-sorts the
actual closure:

  B1  Iut/Concrete/LocalTheory.lean
  B2  Iut/Concrete/LocalConstruct/Packet.lean
  B3  Iut/Concrete/LocalConstruct/Arithmetic.lean
  B4  Iut/Concrete/LocalConstruct/Integral.lean
  B5  Iut/Concrete/LocalConstruct/Indeterminacy.lean
  B6  Iut/Concrete/LocalConstruct/MaximalOrder.lean
  B7  Iut/Concrete/LocalConstruct/Archimedean.lean
  B8  Iut/Concrete/LocalConstruct/Volume.lean
  B9  Iut/Concrete/LocalConstruct/TensorIntegral.lean
  B10 Iut/Concrete/LocalConstruct/ScaleVolume.lean
  B11 Iut/Concrete/LocalConstruct/LocalLogShell.lean
  B12 Iut/Concrete/LocalConstruct/LogShell.lean
  B13 Iut/Concrete/LocalConstruct/Admissible.lean
  B14 Iut/Concrete/LocalConstruct/ThetaAdmissible.lean
  B15 Iut/Concrete/LocalConstruct/LogLattice.lean
  B16 Iut/Concrete/LocalConstruct/FactorShell.lean
  B17 Iut/Concrete/LocalConstruct/ArchLogShell.lean
  B18 Iut/Concrete/LocalConstruct/ArchIndAut.lean
  B19 Iut/Concrete/LocalConstruct/IndAut.lean
  B20 Iut/Concrete/LocalConstruct/LocalDifferent.lean  (needs PadicLogVolume.TraceDuality)
  B21 Iut/Concrete/LocalConstruct/Prop14Lattice.lean
  B22 Iut/Concrete/LocalConstruct/ShellBound.lean
  B23 Iut/Concrete/LocalConstruct/Prop14.lean
  B24 Iut/Concrete/LocalConstruct/Hull.lean
  B25 Iut/Concrete/LocalConstruct/ResidueField.lean

Dependency order is B1 < ... < B25 as listed (plus internal edges the script
recomputes); B20/B21/B22 are only needed for shellExcess_eq_tame and
logShellRadius; without them, a smaller B set B1-B19 supports componentVol,
leastHull, archDefect and ind2. Check -Analyze missing list before -Port.

Expected result after D1/D2: no TemperedFundamentalGroups, no Anabelian.Tempered,
no Cor312.ThetaData in the closure of any B target. Haar.lean is already ported as
Mzk1PortedLocalConstructActual.lean (A866/A877); do not duplicate unless a fresh
copy is wanted.

## 3. Phase 4 copy-only manifest for hull extraction script

These declarations live in TG-blocked files and must be copied by a small
extraction script (not imported). Destination files are our
tmp/sheaf/xif/paper/Mzk1Ported*Actual.lean. The extraction script should print a
report of every copied declaration and every unresolved dependency.

### VcI.lean
| symbol | line | destination |
|---|---|---|
| orderVol | 93 | Mzk1PortedPacketTermsActual.lean |
| orderVol_nonpos | 102 | Mzk1PortedPacketTermsActual.lean |
| shellExcess | 158 | Mzk1PortedPacketTermsActual.lean |
| componentVol_tensorLogShell_eq | 165 | Mzk1PortedPacketTermsActual.lean |
| shellExcess_eq_tame | 414 | Mzk1PortedPacketTermsActual.lean |
| componentVol_tensorLogShell_eq_tame | 427 | Mzk1PortedPacketTermsActual.lean |
| componentVol_leastHull_tensorLogShell_eq_tame | 435 | Mzk1PortedPacketTermsActual.lean |
| logShellRadius | 464 | Mzk1PortedPacketTermsActual.lean |
| exists_isGreatest_logShellRadius | 469 | Mzk1PortedPacketTermsActual.lean |
| vcIPacket | 683 | Mzk1PortedPacketTermsActual.lean |
| hullPacket | 689 | Mzk1PortedPacketTermsActual.lean |
| defectPacket | 703 | Mzk1PortedPacketTermsActual.lean |
| packetVol_vcI | 707 | Mzk1PortedPacketTermsActual.lean |
| packetVol_hull_vcI | 716 | Mzk1PortedPacketTermsActual.lean |
| hullPacket_sub_vcIPacket | 725 | Mzk1PortedPacketTermsActual.lean |
| logVol_vcI_eq | 736 | Mzk1PortedPacketTermsActual.lean |
| logVol_hull_vcI_eq | 741 | Mzk1PortedPacketTermsActual.lean |
| defectPacket_nonneg | 770 | Mzk1PortedPacketTermsActual.lean |
| vcIPacket_finite | 794 | Mzk1PortedPacketTermsActual.lean |
| hullPacket_finite | 806 | Mzk1PortedPacketTermsActual.lean |
| IsTamePrime | 819 | Mzk1PortedPacketTermsActual.lean |
| hullPacket_tame | 844 | Mzk1PortedPacketTermsActual.lean |
| defectPacket_tame | 857 | Mzk1PortedPacketTermsActual.lean |

### Gap.lean
| symbol | line | destination |
|---|---|---|
| leastHull | 87 | Mzk1PortedLeastHullActual.lean |
| leastHull_subset | 93 | Mzk1PortedLeastHullActual.lean |
| leastHull_eq | 97 | Mzk1PortedLeastHullActual.lean |
| exists_leastHull_eq | 107 | Mzk1PortedLeastHullActual.lean |
| leastHull_smul_integral | 138 | Mzk1PortedLeastHullActual.lean |
| leastHull_units_smul | 148 | Mzk1PortedLeastHullActual.lean |
| shellDefect | 438 | Mzk1PortedLeastHullActual.lean |
| shellDefect_nonneg | 442 | Mzk1PortedLeastHullActual.lean |
| shellDefect_eq_zero | 447 | Mzk1PortedLeastHullActual.lean |
| archDefect | 459 | Mzk1PortedArchDefectActual.lean |
| archDefect_nonneg | 463 | Mzk1PortedArchDefectActual.lean |
| archDefect_pos | 468 | Mzk1PortedArchDefectActual.lean |
| thetaComponent_finite_of_not_bad | 725 | Mzk1PortedPilotAlgebraActual.lean |
| ind2Term | 747 | Mzk1PortedInd2Actual.lean |
| ind2Term_nonneg | 756 | Mzk1PortedInd2Actual.lean |
| ind2Term_eq_zero | 771 | Mzk1PortedInd2Actual.lean |
| gapTerm_nonneg | 646 | optional: Mzk1PortedGapTermsActual.lean |
| gapAt_nonneg | 657 | optional |
| gapHullAt | 895 | optional; not needed for M=A-R |

### Wall/Ind3.lean and Wall/Rss.lean
| symbol | line | destination |
|---|---|---|
| vcIComp | Iut/Wall/Ind3.lean:58 | Mzk1PortedPilotAlgebraActual.lean |
| vcIComp_admissible | Ind3.lean:64 | Mzk1PortedPilotAlgebraActual.lean |
| vcIAt | Ind3.lean:80 | Mzk1PortedPilotAlgebraActual.lean |
| hullOf | Iut/Wall/Rss.lean:328 | Mzk1PortedPilotAlgebraActual.lean |

### IdentifiedCopies.lean
| symbol | line | destination |
|---|---|---|
| componentVol_units_smul | Iut/Wall/IdentifiedCopies.lean:67 | Mzk1PortedScaleVolumeActual.lean |
| units_smul_mem_admissible | IdentifiedCopies.lean:82 | Mzk1PortedScaleVolumeActual.lean |

### ThetaRegion.lean (copy only; source TG-blocked)
| symbol | line | destination |
|---|---|---|
| scaleEltAt | 126 | Mzk1PortedPilotAlgebraActual.lean |
| scaleElt | 136 | Mzk1PortedPilotAlgebraActual.lean |
| thetaFiniteOn | 170 | Mzk1PortedPilotAlgebraActual.lean |
| thetaFinite_eq | 261 | Mzk1PortedPilotAlgebraActual.lean |
| thetaComponentOn | 178 | Mzk1PortedPilotAlgebraActual.lean |
| thetaComponent | 257 | Mzk1PortedPilotAlgebraActual.lean |

Every copied declaration must retain its exact body and type; no arbitrary
replacement. The extraction script must list unresolved dependencies (e.g.
InitialThetaData fields, label types, qroot/qOrder); those are supplied by
Mzk1PortedPilotContextActual.lean, not by importing ThetaData.

## 4. Phase 3-5 target outline handed to mainline

Phase 3 (direct script, after Batch A):
- port Cor312/LogVolume closure to Mzk1PortedLogVolumeActual.lean and
  Mzk1PortedContainerActual.lean.
- copy RHSData/rhs definition from RightHandSide.lean:65/99/107 into
  Mzk1PortedRHSActual.lean with a generic container/thetaPilot context; no
  InitialThetaData import.

Phase 4:
- copy section 3 manifest into:
  Mzk1PortedPilotContextActual.lean,
  Mzk1PortedPilotAlgebraActual.lean,
  Mzk1PortedLeastHullActual.lean,
  Mzk1PortedPacketTermsActual.lean,
  Mzk1PortedInd2Actual.lean,
  Mzk1PortedArchDefectActual.lean.

Phase 5:
- Mzk1PortedRExpansionActual.lean (packetVol(thetaHull) expansion);
- Mzk1PortedMNonnegActual.lean (qPositiveSum/M=A-R), using
  Mzk1ScalingNormalizationActual (already our file).

## 5. Verification gates after Port

For each scripted batch:
1. -Analyze: missing list must not contain TemperedFundamentalGroups,
   Anabelian.Tempered, Anabelian.GenuineEtale, Cor312.ThetaData, or
   ThetaLocalConstruct.Data.
2. -Port: check topo_order.txt and that copied files import only
   tmp.external.ported.<Name>.* plus Mathlib.
3. hand to watchdog; no stepxi -Compile.
4. first failure triage: padic/Mathlib API drift is a mechanical rule
   (tools/port_fix_rules.txt); missing TG module means stop and report
   TG-DRIFT-NOTES.

## 6. Summary

- Direct script: Batch A (Cor312 pure container/logvolume) + optional PadicLogVolume;
  no TG.
- Staged script: Batch B LocalConstruct after D1 (LocalTheory import -> Mathlib)
  and D2 (minimal Ordp lower block); no TG in closure.
- Copy-only: Gap/VcI/Ind3/Rss/IdentifiedCopies/ThetaRegion definitions in section 3;
  hull extraction script consumes this manifest.
- Do not script-port Gap/VcI/ThetaData/Anabelian/TG; do not import them.
