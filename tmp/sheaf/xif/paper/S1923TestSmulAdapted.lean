import tmp.sheaf.xif.paper.S1923UniversalFormula
open WeierstrassCurve
example {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K) (x y : K) (h : W.Nonsingular x y) :
    W.Point := (7 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.Point)
