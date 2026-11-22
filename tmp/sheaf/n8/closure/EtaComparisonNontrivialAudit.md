# EtaComparisonNontrivial audit

Date: 2026-10-24
Auditor: transport
Audited file: tmp/sheaf/n8/closure/EtaComparisonNontrivial.lean
Lines: 88
SHA256: DA83F9C49452AE99BC293EBB395C09FB53B5B6B8701E2B21E719415580F24F63

No Lean changes made by this audit.

## 1. Codomains

Both interfaces have codomain Multiplicative Real:

- EtaQMapInterface.etaQ : EtaQActual.Rval X -> Multiplicative Real
- EtaAnabMapInterface.etaAnab : Multiplicative Real -> Multiplicative Real

Multiplicative Real is the ETA-5 real value-group target, but in this file it is
used as a common codomain for both maps without the ETA route's actual
preLogShell/logShell carriers. It is therefore a scalarized/trivialized common
line, not the ETA route Rss.

The actual ETA route (EtaRouteInterface.lean) has:

- Rval := (nativeLocalShell X).preLogShell, a subset of K;
- Rss := (nativeLocalShell X).logShell, a subset of K;
- EtaQ : Rval -> Rss, a |-> (pStar)^(-1) * a;
- EtaAnab : Rss -> Rval, b |-> pStar * b.

Our file does not use preLogShell, logShell, or pStar at all. Its codomains are
not the ETA route carriers.

## 2. Independence of etaQ / etaAnab

etaQ is actual: etaQMapInterface is the unitNormLogDegree map. The theorem
etaQMapInterface_qUnit proves its q-unit image is etaPilot. This part is actual.

etaAnab is only an interface:

  theorem missing_etaAnabMapInterface :
      Nonempty (EtaAnabMapInterface X) := by sorry

No etaAnab map is constructed, and no relation to the actual EtaRouteInterface
EtaAnab is stated. Thus the two maps are "independent" only because etaAnab is a
named gap, not because two actual constructions were compared.

## 3. value_eq is only a pilot fixed point

The target value_eq is:

  qInterface.etaQ (etaQUnit X) = anabInterface.etaAnab (etaPilot X)

But etaQMapInterface_qUnit gives:

  qInterface.etaQ (etaQUnit X) = etaPilot X

so value_eq is equivalent to:

  etaPilot X = anabInterface.etaAnab (etaPilot X)

This is a fixed-point condition at the pilot, not a commutative square between
independent etaQ and etaAnab routes. It does not identify an EtaQ image with an
EtaAnab image at a non-fixed actual point, and it does not use the ETA route
preLogShell/logShell scaling.

## 4. Inverse laws

The file correctly does not assert inverse laws. There is no field
etaAnab after etaQ = id or etaQ after etaAnab = id. This part of the target
design is compliant.

## 5. Relation to the eta route

Verdict: not eta-route compliant.

- It replaces the actual preLogShell/logShell carriers by Multiplicative Real.
- It does not construct the real-to-real etaAnab map.
- value_eq is a pilot fixed-point, not a square/value equality of two actual
  independent maps.
- The only named gap is the etaAnab interface; the actual eta route already has
  an EtaAnab map, so the file does not explain how the independent map relates to
  it.

## 6. Exact correction

Use the actual ETA route carriers and maps, and keep Multiplicative Real only as
a scalar observation.

Correction target (sketch, not Lean-edited):

  abbrev Shell := EtaRouteInterface.NativeShell X
  abbrev RvalPre := (Shell).preLogShell
  abbrev Rss := (Shell).logShell

  def pStarScalar : Multiplicative Real :=
    Multiplicative.ofAdd (Real.log ‖((Shell).pStar : Shell.K)‖)

  def rvalScalar (a : RvalPre) : Multiplicative Real :=
    Multiplicative.ofAdd (Real.log ‖a.1‖)

  def rssScalar (b : Rss) : Multiplicative Real :=
    Multiplicative.ofAdd (Real.log ‖b.1‖)

  theorem etaQ_scalar_square (a : RvalPre) :
      rssScalar (EtaRouteInterface.EtaQ X a) =
        pStarScalar⁻¹ * rvalScalar a

  theorem etaAnab_scalar_square (b : Rss) :
      rvalScalar (EtaRouteInterface.EtaAnab X b) =
        pStarScalar * rssScalar b

The two square identities are actual log-multiplicativity consequences of the
ETA route scaling maps. They compare the actual EtaQ and EtaAnab images in the
scalar value group and do not state inverse laws.

If the scalar observation rssScalar is not accepted as the eta route readout,
the exact named gap must be the scalar map itself:

  def RssScalarMap : Prop :=
    Nonempty (Rss -> Multiplicative Real)

with its production construction; do not encode it as a free etaAnab interface.

The corrected nontrivial comparison should be a square:

  for a : RvalPre,
    rssScalar (EtaQ a) = (pStarScalar)⁻¹ * rvalScalar a

or the corresponding etaAnab-side identity. It must not reduce to
etaPilot = etaAnab etaPilot.

## 7. Status

EtaComparisonNontrivial is archived as a non-eta-route target. Its only
reusable content is the actual etaQ map etaQMapInterface and the proved
etaQMapInterface_qUnit. The independent etaAnab interface and value_eq must be
replaced by the actual EtaRouteInterface maps and the scalar square identities
above.
