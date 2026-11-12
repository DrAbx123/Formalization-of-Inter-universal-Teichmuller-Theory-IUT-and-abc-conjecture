# Weight strict additivity and max formula: actual

## BUILT (EXIT=0)
S2482WeightStrictActual.lean (imports S2482WeightAdditivityActual):
- coords_neg.
- W_neg : W (-z) = W z.
- W_add_eq_of_lt (z w) : W z < W w -> W (z + w) = W w.
- W_add_eq_max_of_ne (z w) : W z != W w -> W (z+w) = max (W z) (W w).
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Proof
W_add_le gives <=. For >=, assume W(z+w)<W(w); apply W_add_le to (z+w) and -z,
using W_neg, to get W w <= max (W(z+w))(W z) < W w, contradiction.
Thus W(z+w)=W w. The max formula follows by symmetry and max_eq_left/right.

## Consequence
Combined with v2 W_mul and W_eq, the weight is nonarchimedean and multiplicative:
  W(z*w)=W z + W w, W(z+w)<=max, and equality when unequal.
Next: phi preserves norm filtration -> phi(x)=x -> phi(y)=±y -> sign; then 2-Yoneda.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482WeightStrictActual.lean
EXIT=0; SHA256 A15822E26783EE8E31E21BB623E40E4689FA1DF798C5D6BD908137F505DF1F77
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482WeightStrictActual.olean
olean SHA256: BC262A3BCB666F3E4FA94A3F5C0620860962FF8F1DE6AE32123C0A7A7259BDC9
axioms: trio