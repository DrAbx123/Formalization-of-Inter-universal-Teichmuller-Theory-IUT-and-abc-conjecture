# Paper-level xi-f from-scratch build plan

User directive: 火力全开去写，别急编译。Write bulk first; unified compile later.

Target: actual IUT III xi-f, not value-layer surrogate.

## Module order

```text
QPI-1 QPilotObjectActual.lean
  actual q-pilot object at (1,0): strip, arithmetic line bundle, log-Kummer representation,
  (1,0) binding; no PaperQPilotObject obligation field left as an assumption if constructible.

QPI-2 QPilotLogActual.lean
  actual q scalar, positivity, q != 1, signed -|log q|, identification with paper QPaper.

TH-1 ThetaHullActual.lean
  actual 1,circ U hull: compactness, procession average, Haar/log-shell normalization.

TH-2 SignedHullLogActual.lean
  actual signed -|log Theta| from hull determinant/log-volume; no ENNReal clamp.

OM-1 OModuleActual.lean
  actual rank-one arithmetic line bundle, O-module/localization, determinant, integral structure.

IND-1 IndeterminaciesActual.lean
  actual Ind1/Ind2/Ind3 actions and invariance of log-volume/region.

SHE-1 SHELandingActual.lean
  actual SHE landing: output data expressed in 1,circ localizations; no interface-only witness.

IPL-1 IPLActual.lean
  actual IPL link isomorphisms and compatibility.

APT-1 APTActual.lean
  actual APT transport/evidence.

LINK-1 ThetaLinkActual.lean
  actual Theta-link comparison; derives -|log q| in R_{<= -|log Theta|} from link.

XIF-1 PaperXiFProof.lean
  final source xi-f from QPI/TH/OM/IND/SHE/IPL/APT/LINK.

ASM-1 PaperAssembly.lean
  compile gate and conditioned/unconditional assembly; exact obligations listed.
```

## Hard rules

1. Only actual source/project types; no PUnit/Unit/True/toy carriers.
2. A missing object is a structure with actual fields plus exact obligation fields; no axiom/sorry.
3. Do not import value-layer surrogate for paper conclusions.
4. Write bulk first; compile at the batch gate. Keep imports minimal and namespaces unique.
5. If a file cannot close, record exact obstruction and keep definitions/lemmas that do compile later.
6. Paper-level files under tmp/sheaf/xif/paper/; one owner per file.
