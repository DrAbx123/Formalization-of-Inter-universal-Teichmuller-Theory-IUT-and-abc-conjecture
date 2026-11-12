# S2482: Q(i) curve and InitialThetaArithmeticData actual

Layer: O (IUT I Definition 3.1 arithmetic data over F=Q(i)).

## BUILT (EXIT=0)
- S2482Curve : WeierstrassCurve F, y^2 = x^3 - x (a1=a2=a3=a6=0, a4=-1).
- S2482Curve_Δ : Δ = 64, hence nonzero over Q(i).
- instance : S2482Curve.IsElliptic.
- S2482PuncturedCurve : PuncturedEllipticCurve F with projective puncture 0.
- S2482_finrank : Module.finrank Q F = 2 (AdjoinRoot power basis).
- instance S2482_quadratic : Algebra.IsQuadraticExtension Q F.
- S2482_isGalois : IsGalois Q F (via quadratic extension + separability).
- S2482Arithmetic.l5 : PrimeGeFive value 5.
- S2482Arithmetic.thetaTower : ThetaFieldTower 5 Q F F (sqrt(-1), degree 2 coprime 5).
- S2482Arithmetic.arithmeticData : InitialThetaArithmeticData 5, curve S2482PuncturedCurve.

## Artifacts
Curve: tmp/sheaf/xif/paper/S2482QiCurveActual.lean
- EXIT=0; SHA256 93BD2946DF5BDE7A2A315A667CF96FCF0DDEFB8EC67E7F9A01E431319AA60221
- olean SHA256 B5E39B9C9831CCD8C0FF151AB859493896CDDA644D828E3941534CDE2B382D2B
Arithmetic: tmp/sheaf/xif/paper/S2482QiArithmeticActual.lean
- EXIT=0; SHA256 435C8EC5647928547AAE38CC7C887D84C055D7B42C356C3D61D60C29163EF6F3
- olean SHA256 902CCF524923FD639BCF633FAABB9BF8E700061FB7C543B48FA36FB693251A6B

All new theorems/defs depend on axioms propext, Classical.choice, Quot.sound; no sorryAx.
Input S2480QiActual reused (F=AdjoinRoot(X^2+1), HasSqrtNegOne); no redefinition.