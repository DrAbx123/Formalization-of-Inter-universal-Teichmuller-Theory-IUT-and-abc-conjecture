# ETA Remark 3.10.2 square audit

Date: 2026-10-24
Auditor: transport
Source square: IUT III, Remark 3.10.2: env -> gau -> LGP -> lgp, with the
fPlaceShell / source action / Gaussian / lgp / region data.
No Lean files changed.

Research-side reference:
tmp/api3-kummer-evaluation-20261016/SourceKummerEvaluationArrows.final.lean
This is the frozen research record for the reduced four-corner Kummer
evaluation square on the old kernel; it is not the current N8 closure.

## 1. Component map

### env / fPlaceShell
Current actual carriers:
- LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput X (S/L slice);
- LeanFormal.IUT.N8Closure.NativeC3.nativeFPlaceOverBad X / nativeFPlaceAtPrime X;
- LeanFormal.IUT.N8Closure.C2Native.nativeLocalShell X, whose K is the
  actual CommonPrimeCompletion, with actual preLogShell and logShell.

Status: fPlaceShell carrier is actual. The finite-place shell
(nativeLocalShell) has actual preLogShell/logShell and actual pStar; it is
the best current fPlaceShell analogue.

Exact gap: no N8 type named fPlaceShell; nativeLocalShell is a single local
log-shell datum, not the full finite-place shell functorial object.

### source action
Production structures exist in
LeanFormal.IUT.IUTII.Kummer.SourceLogShellActionCompatibility, and the old
research file has sourceAction / targetAction records.  In the current N8
closure there is no constructed actual source action on nativeLocalShell.

Status: exact gap.
Required exact target: a source action G -> MulAut of the actual shell/unit
carrier, with the actual production action compatibility; no free action.

### gau / Gaussian
Current actual Gaussian data:
- C3.thetaPacket : FiniteThetaPacket l, with Gaussian exponent gaussExponent;
- C3.roots / C3.kummerClass / C3.rootChange using the actual qUnit and
  Gaussian exponents;
- C7 theta completion uses C3.qUnit and the label's Gaussian exponent.

Status: only the Gaussian exponent/scalar action on the theta packet is
actual.  The Gaussian prime-strip / Gaussian vertex as a full object is not
constructed in N8.

Exact gap: a Gaussian vertical prime-strip (or Gaussian Hodge theater data)
with actual theta/Gaussian action and value-group/region compatibility.

### LGP
No current N8 LGP-monoid object.  The only LGP-related formalization is the
frozen research record in
tmp/api3-kummer-evaluation-20261016/SourceKummerEvaluationArrows.final.lean
plus the old source Kummer layer records.

Status: exact gap for the current N8 route.

### lgp
No current N8 local Galois prime-strip / lgp object.  The old research file
explicitly notes that the LGP -> lgp arrow is outside its composite.

Status: exact gap.

### region
Current actual region components:
- P6 finite-place unit-sphere Adm and relaxed finite readout;
- P6NonarchSphereMassActual: actual positive finite unit-sphere Haar mass;
- P6NonarchAdmClosed: actual finite-place Adm from unit-sphere mass;
- P6NonarchSphereMassActual provides the actual sphere/ball vocabulary.

Status: actual for the finite-place relaxed region/Adm slice, but this is not
the paper's env -> gau -> LGP -> lgp region object.  No full finite-place shell
region with source action and Gaussian compatibility is constructed.

## 2. Arrow table

| id | paper arrow | current Lean component | status |
|---|---|---|---|
| E1 | env -> fPlaceShell | N8NativeInput, nativeFPlaceOverBad, C2Native.nativeLocalShell | actual carrier; exact type named fPlaceShell missing |
| E2 | fPlaceShell -> source action | production SourceLogShellActionCompatibility records; no N8 actual action | OPEN exact gap |
| E3 | env -> gau (Gaussian) | C3.thetaPacket, gaussExponent, C3.roots/kummerClass | partial actual (Gaussian exponent only); full Gaussian vertex OPEN |
| E4 | gau -> LGP | old research SourceKummerEvaluationArrows; no current N8 LGP | OPEN exact gap |
| E5 | LGP -> lgp | none in current N8; old research excludes LGP -> lgp | OPEN exact gap |
| E6 | lgp -> region | P6 finite unit-sphere/Adm/readout only | partial actual region slice; paper region OPEN |
| E7 | source action commutes with Gaussian | no N8 action/Gaussian square | OPEN exact gap |
| E8 | env -> lgp composite | EtaRouteInterface actual preLogShell -> logShell scaling maps (local), not full lgp | partial actual local scaling; full square OPEN |

The square is not claimed.  The only actual pieces are:
- the native finite-place shell carrier nativeLocalShell;
- the Gaussian exponent/theta packet scalar data in C3;
- the actual EtaRouteInterface preLogShell/logShell scaling maps;
- the finite-place P6 unit-sphere relaxed Adm/readout.

The arrows E2, E4, E5, E7 and the full E6 target are exact gaps.  No arrow is
replaced by a free map or a trivial Real comparison.

## 3. Exact gap list

G1. fPlaceShell type:
   A named N8 structure with actual nativeLocalShell / preLogShell /
   logShell / pStar data, not a free Set/Real field.

G2. source action:
   An actual action of the finite Galois/source group on the fPlaceShell
   carrier, with production action compatibility.  Formal target to be
   derived from SourceLogShellActionCompatibility, not assumed.

G3. Gaussian vertex:
   A Gaussian prime-strip/theater object tied to C3.thetaPacket and the
   actual Gaussian exponents.  Current C3 only has the exponent/theta packet.

G4. LGP vertex:
   An actual LGP-monoid/prime-strip object.  Current N8 has none; old
   research records are frozen, not current closure.

G5. lgp vertex:
   An actual local Galois prime-strip object.  Current N8 has none.

G6. square commutations:
   The four-corner env -> gau -> LGP -> lgp commutation as an actual
   commutative square, with no inverse-law substitute and no scalarized
   common line.

G7. paper region:
   The region object attached to the full fPlaceShell/source-action/Gaussian/
   LGP/lgp square.  Current P6 finite unit-sphere region is only a local
   relaxed Adm/readout slice.

## 4. Next executable checklist

1. Write EtaFPlaceShellActual.lean: define the exact fPlaceShell structure
   from NativeC3.nativeFPlaceOverBad, C2Native.nativeLocalShell,
   preLogShell, logShell, pStar; actual construction, no sorry.
2. Write EtaSourceActionActual.lean: define the exact source-action target and
   attempt construction from the production
   SourceLogShellActionCompatibility records; if no production action on
   nativeLocalShell, one theorem-level named gap with the exact action type.
3. Write EtaGaussianVertexActual.lean: define the exact Gaussian vertex
   structure from C3.thetaPacket, gaussExponent, roots/kummerClass; actual
   exponent part; named gap for the full Gaussian prime-strip.
4. Write EtaLGPVertexActual.lean: define the exact LGP vertex target.  Do not
   import the frozen research record as a constructed object; state the
   missing production LGP construction as a named gap.
5. Write EtaLGPLocalVertexActual.lean: define the exact lgp vertex target and
   named gap; no inverse laws.
6. Write EtaRemark3102SquareActual.lean: assemble the actual fPlaceShell and
   Gaussian exponent parts, then state the four corners and the exact
   commutation targets (E7/E8) with named gaps only where the preceding
   vertices are missing.
7. Audit any attempted square: no use of etaAnab inverse laws, no scalarized
   common Real line, no arbitrary action/region data.  The square must be a
   genuine commutative square of the actual carriers.

## 5. Status

Remark 3.10.2 is not formalized as a square in the current N8 closure.  The
audit records the exact component status and the next package sequence.  No
Lean file was modified.
