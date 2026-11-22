# S2780 Gaussian y^2 = x^3 - x: 2-adic data audit

Date: 2026-11-07
Curve: E : y^2 = x^3 - x over F = Q(i)
Place: p over 2, i.e. p = (1+i)

## 0. UPDATE: Sage actually available at WSL path

The Sage environment IS present at:

    wsl -d Ubuntu-24.04 -- /opt/miniconda/envs/sage/bin/sage

Verified command:

    E = EllipticCurve([0,0,0,-1,0])
    K.<i> = QuadraticField(-1)
    EK = E.change_ring(K)
    P = K.ideal(1+i)
    EK.local_data(P)

Actual Sage output (2026-11-07):

    Local data at Fractional ideal (i + 1):
    Reduction type: bad additive
    Local minimal model: Elliptic Curve defined by y^2 = x^3 + (-1)*x over
      Number Field in i with defining polynomial x^2 + 1
    Minimal discriminant valuation: 12
    Conductor exponent: 6
    Kodaira Symbol: I2*
    Tamagawa Number: 4

Note: EK.minimal_model(P) is not available as a method in this Sage version;
local_data already prints the local minimal model.  Use integral_model() for an
integral model if needed.

### Consequence

    HasStableReductionAt P = HasGoodReductionAt P or HasMultiplicativeReductionAt P.

Sage says bad additive, Kodaira I2*, so neither good nor multiplicative.
Therefore, at P = (1+i) over 2:

    hstable : forall p, gaussianCurve.HasStableReductionAt p

is FALSE for E: y^2 = x^3 - x over Q(i).

So S2773 gaussianClauseA cannot be instantiated for this curve.  ClauseA for
this particular Gaussian curve is infeasible; a semistable curve (or a different
base field/source curve) must be used instead.

Do not attempt to prove hstable for this curve.

## 1. Environment status (historical, superseded by section 0)

Requested: run Sage local reduction and record minimal model / Kodaira type /
stabilization data.

Actual environment check:

    Get-Command sage        -> not found
    Get-Command sagemath    -> not found
    Get-Command gp          -> not found (the name gp is only a PowerShell alias for Get-ItemProperty)
    WSL Ubuntu-24.04         -> command -v sage: empty
    WSL Ubuntu-24.04         -> command -v gp: empty
    python -c "import sage" -> ModuleNotFoundError: No module named 'sage'
    conda/mamba/docker       -> not found

Conclusion: Sage is NOT available in this session. No Sage output was produced.
Therefore no minimal model, Kodaira type, or stabilization claim is made here.

## 2. Lean-actual rational data

The rational curve y^2 = x^3 - x is actual in Lean:

    curveY2EqX3SubX : WeierstrassCurve Q
    curveY2EqX3SubX_isElliptic
    curveY2EqX3SubX.Delta = 64
    curveY2EqX3SubX.j = 1728

Related Lean actual:

    S2765CurveOutsideTwoActual.localCurve_isIntegral
    S2765CurveOutsideTwoActual.localCurve_delta
    S2765CurveOutsideTwoActual.localCurve_delta_isUnit
    S2765CurveOutsideTwoActual.localCurve_hasGoodReduction
    S2765CurveOutsideTwoActual.localCurve_hasGoodReductionOnMinimalModel

These are outside-2 results only.

## 3. Elementary 2-adic invariants (hand computation, not Sage)

In Q(i), the prime p = (1+i) is the unique prime over 2, with

    e = 2, f = 1, v_p(2) = 2.

For the displayed model E: y^2 = x^3 - x:

    Delta = 64 = 2^6,      v_p(Delta) = 12
    c4    = 48 = 2^4 * 3,  v_p(c4)   = 8
    c6    = 0,             v_p(c6)   = infinity
    j     = 1728,          v_p(j)    = 12 - 8 = 4 (as a p-adic valuation of the rational value)

The displayed model is not minimal at p in the naive sense v_p(Delta) = 12
because minimality requires v_p(Delta) < 12; the base-changed model therefore
cannot be used directly to read the Kodaira type.

## 4. What is NOT claimed

Not computed / not claimed:

- minimal Weierstrass model at p = (1+i);
- v_p(Delta_min), v_p(c4_min), v_p(c6_min) of that minimal model;
- Kodaira fiber type (I0, I0*, I_n, II, III, IV, etc.);
- good / multiplicative / additive reduction at p;
- stable reduction at p;
- any Lean theorem or inhabitant of HasStableReductionAt at p over 2.

The existing Lean conditional ClauseA (S2773) still takes

    hstable : forall p : FinitePlace GaussianField,
      gaussianCurve.HasStableReductionAt p

as an explicit input.  This file supplies no proof of hstable.

## 5. Exact Sage commands to run when Sage is available

    E = EllipticCurve([0,0,0,-1,0])          # y^2 = x^3 - x over Q
    K.<i> = QuadraticField(-1)
    EK = E.change_ring(K)
    P = K.ideal(1+i)                          # prime over 2
    EK.local_data(P)                          # Kodaira type, local minimal model
    EK.minimal_model(P)
    EK.conductor(P)

Record:

    EK.local_data(P)        -> Kodaira type / reduction type
    EK.minimal_model(P)     -> [a1,a2,a3,a4,a6] over K
    EK.conductor(P)         -> conductor exponent
    EK.tate_curve(P)        -> only if multiplicative

Then, and only then, write the resulting values into a Lean-facing data record.
Do not convert this markdown into a Lean theorem.

## 6. Status

    Sage data: NOT PRODUCED (Sage not installed)
    Lean actual: rational curve and outside-2 local data only
    p over 2 minimal model / Kodaira type / stable: OPEN
    SourceClauseA: CONDITIONAL on hstable (S2773)

This file is an audit record, not a proof and not a stable-reduction claim.
