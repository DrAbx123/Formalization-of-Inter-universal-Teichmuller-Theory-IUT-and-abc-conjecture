# C9 actual archimedean r_inf / angular term from the E_j skeleton

Task: task-232. Owner: qside. Date: 2026-10-25.
Stage: natural-language/exact-source research only; no Lean/Project edits; no
arbitrary r_v; no U/B normalization ad hoc; only this file written.

## 0. Verdict

The E_j/F/K skeleton does **not** determine an actual archimedean radial radius
`r_inf` or angular term for the IUT Θ-pilot hull.  E_j supplies an actual
elliptic curve and a conditional finite-place/field skeleton; it does not supply
the archimedean possible-image set of the source Θ-pilot object.  Consequently:

- no exact `r_inf` can be computed from the current skeleton;
- the only paper-level bound available is the IV container upper bound
  `h_inf <= A_arc = ((l+5)/4) log pi` (conditional on the target-container
  inclusion of the actual hull), not an actual value;
- no lower bound `h_inf >= D` is available; the IV normalization normalizes
  `B_I` to zero and gives no positive lower bound on the actual image;
- attainment of the maximal-container bound is not established; the bound is
  an upper bound, and E_j gives no actual image filling the container.

The correct classification is: local finite E_j data actual/conditional;
archimedean `r_v`, angular term, lower bound, and container attainment missing.

## 1. Inputs

| file | SHA256 | role |
|---|---|---|
| `C9-EJ-COMPLETION-20261025.md` | `08F308CD1F656520BE3668B0C62776BA8CD38AFB66A34C7BD5522696BC7EA226` | E_j/F/K skeleton |
| `C9-AUDIT-EJ-20261025.md` | `55035AC1BCC9D82B4AB91F0C16276FA008635F97A3B446644D844306DF992ADB` | E_j audit |
| `C9-HAFULL-COORDINATES-20261025.md` | `06299F26383AF7DA73DC8BB844F2FEF7C939D486BD922CEC5E1785F0DF0CBBF4` | H_A/U/W coordinates (context) |
| `C9-GLOBAL-ASSEMBLY-BINDING-20261025.md` | `0888F47DC5D5DC21410F39FF7A81D4315E55FABD84E882BC3D17FDB27A25D9FA` | binding B_I-zero assembly |
| `C9-NORMALIZATION-DECISION-20261025.md` | `5E969DFBFB3E08B2C2CA5A7859683F914FEB3236486B51691FD4D77BE774C78D` | B_I-zero decision |
| `C9-ARCH-GLOBAL-20261025.md` | `524E078AD85C72067627F006D165A724436E1BA508E86475C5F991860586E489` | prior arch template (superseded in normalization) |

Binding corrections retained:

- E_j exact q is `q=p^6+744p^12+O(p^18)`, not `p^6`;
  `qhat=q^{1/82}=pi^3 v`, `v in 1+p^6 Z_p`, order 3.
- `K_v e=41,f=1` and full C_K/V/ε remain conditional/formal; explicit
  equations and mod-41 image are missing.
- B_I-zero is the binding archimedean normalization (task-182/208); shell-pi
  formulas are withdrawn.
- Archimedean `r_v` and angular terms were already marked missing in the
  prior corrected assembly.

## 2. What the E_j skeleton actually provides

### 2.1 Finite/local data (actual or conditional)

E_j is the actual curve

```text
j0 = 1/p^6,  p=12301,
E: y^2 = x^3 - 3 j0/(j0-1728) x - 2 j0/(j0-1728),
Delta = 2985984 p^6/(1-1728 p^6)^3,  v_p(Delta)=6.
```

At p it has multiplicative I_6, actual q expansion
`q=p^6+744p^12+O(p^18)`, and `qhat=pi^3 v` with `v` a p-adic unit.  At 2,3 the
minimal model is good; the D-primes are potential good additive and are
semistabilized.  The field

```text
F = Q(i, E[6], F_sem),   K = F(E[41])
```

is an actual formal Galois skeleton; `F` contains `i`, and `K/F` is cut out
by the 41-torsion.  The quotient objects `C_K=[X_K/E[41]]`, `C_F`, the section
`V`, and `epsilon` are source-level formal definitions; explicit equations and
the mod-41 image are missing.

### 2.2 Archimedean fact that does follow

`F` contains `i`, hence `F` has **no real archimedean place**: an embedding
`F -> R` would send `i` to ±i, impossible.  Therefore all archimedean places
of `F` (and of `K`) are complex, `F_v ~= C`, `d_v=2`, and the degree weights

```text
alpha_v = d_v/[F:Q] = 2/[F:Q],   sum_{v|infty} alpha_v = 1
```

hold for the archimedean places.  This is an actual structural fact, but it
does not give the number of places (the exact degree of `F` is conditional on
`F_sem`, `E[6]`, `E[41]` equations), and it does not give any `r_v`.

## 3. What `r_v` would have to be

Under the binding B_I-zero normalization, for an archimedean place `v` of the
base field, a radial hull `B_v(r_v)` has

```text
h_v^rad(B_v(r_v)) = log r_v,
h_inf(C) = sum_{v|infty} alpha_v [ h_v^ang(A_v) + log r_v ],       (3.1)
```

where `r_v` is the radial radius of the **actual Θ-pilot possible-image
archimedean hull**, not the radius of the elliptic curve `E_j` and not an
arbitrary chosen ball.  For a nonradial hull the angular term `h_v^ang(A_v)`
must be retained.

The missing object is therefore

```text
H_C,inf = the actual archimedean component of the holomorphic hull
          of the union of possible Θ-pilot images,
r_v = sup{|x|_v : x in H_C,inf},   A_v = angular projection/trace.
```

Neither the E_j curve nor its `C_K` quotient supplies `H_C,inf` or its
archimedean possible-image set.

## 4. Why E_j does not determine `r_v` or the angular term

### 4.1 Classical uniformization is not the IUT archimedean hull

At a complex embedding, `E_j(C)` is a complex torus `C/Λ_tau` with
`j(tau)=j0`; this gives periods and an analytic coordinate.  But the IUT
archimedean Θ-pilot object is an object in the archimedean tensor packet built
from the source initial Θ-data; its possible-image hull is not the classical
elliptic curve or its period lattice.  The skeleton defines no map

```text
E_j(C) or its period lattice  ->  H_C,inf.
```

Therefore choosing `r_v = |period|`, `r_v = max|x|` over torsion points, or
`r_v = 1` would be an arbitrary assignment prohibited by the task.

### 4.2 Periods are not explicit even classically

`j0=1/p^6` is rational and non-CM (`j0` is not an algebraic integer;
`j0 != 0,1728`), so the period ratio `tau` is not a quadratic imaginary
number and no explicit CM period formula exists.  The equation has huge
rational coefficients, but its complex periods are transcendental analytic
data not supplied in exact form by the frozen skeleton.  Even a numerical
period would not determine the IUT hull without the source map of §4.1.

### 4.3 Explicit fields/embeddings and archimedean places are missing

The skeleton defines `F` and `K` abstractly via torsion fields, but does not
give:

- an explicit polynomial/equation for `F` or `K`;
- the archimedean embeddings of `F`/`K`;
- the explicit `E[6]`/`E[41]` coordinates needed to identify the complex
  conjugates and the unit-circle angular data;
- the source theta function/theta values at those points.

Thus even the archimedean local fields `F_v~=C` and their embeddings are not
enumerated, let alone the possible Θ-pilot images.

### 4.4 The actual complete C is not constructed

The E_j skeleton is not a complete C: it lacks explicit `C_F/C_K`, the `V`
place section equations, `epsilon` coordinates, the bad set beyond the
candidate, the q/BPS/Θ-gluing data, the target column, and the actual
archimedean Θ-pilot object.  The prior E_j audit explicitly lists `actual
archimedean r_v/h_inf` as missing.  Without these, the hull `H_C,inf` is not
even defined.

## 5. Conditional upper bounds only

### 5.1 IV container bound

The only paper-level archimedean bound in the frozen assembly is the IV
container upper bound.  For a fixed `j`, if the actual hull lies in
`pi^{j+1} B_I`, then

```text
h_inf <= (j+1) log pi.                                   (5.1)
```

After the procession average over `j=1,...,m=(l-1)/2`,

```text
h_inf <= A_arc = ((l+5)/4) log pi,
l=41:  A_arc = 11.5 log pi = 13.1643936873...  natural units.   (5.2)
```

Bound (5.2) is an upper bound and is conditional on the target-container
inclusion of the actual possible-image hull.  It gives no information about
the actual `r_v` or angular term inside the container.

### 5.2 Local angular upper bound (conditional)

Under the AbsTopIII angular normalization, the full unit circle has angular
volume `2 pi`, so for an angular region `A_v <= O_v^times`,

```text
h_v^ang(A_v) <= log(2 pi).                               (5.3)
```

This is a local structural upper bound, not an evaluation for the E_j source.
Combining (3.1) and (5.3) gives only a container-relative upper bound; it does
not produce a positive lower bound for `h_inf`.

### 5.3 Shell containment (conditional, weaker)

If the actual archimedean hull happened to lie in the source shell
`I_v={|a|<=pi}`, then under B_I-zero

```text
h_inf <= log pi = 1.1447298858...,                       (5.4)
```

not `h_inf <= 0` and not an equality.  The shell containment itself is not
proved for the E_j skeleton; it is a conditional branch.  Shell-pi normalized
formulas (`log(r/pi)`, `pi p^{d_p}`) are binding-withdrawn.

## 6. No lower bound `h_inf >= D`

The IV normalization sets `log-volume(B_I)=0`; the unit ball gives zero
reference, not a positive lower bound on the actual image.  The container
`pi^{j+1}B_I` is an upper container; a possible image may be much smaller.

Similarly, product-formula constraints are **point-modulus** constraints, not
hull-volume lower bounds.  Under B_I-zero, for a global point `x`,

```text
sum_{v|infty} alpha_v log|x|_v + sum_p alpha_p v_p(x) log p = 0,   (6.1)
h_inf >= - sum_p alpha_p v_p(x) log p                            (6.2)
```

if `x` lies in the radial hull.  For finite-integral `x` the right side is
nonpositive; for a global unit it is zero.  This does not give `h_inf>=D` for
the positive finite deficit `D` of the b=3/b=273 profiles.  In particular, the
conditions `r_v<=pi` and `h_inf<=log pi` are compatible with a very small
actual image; no positive radius/lower bound is supplied by E_j.

Therefore the available lower bound is only the trivial/nonpositive
product-formula point constraint, not the required compensation lower bound.

## 7. Can `h_inf` attain the maximal-container bound?

**Not established, and not computable from the E_j skeleton.**  Attainment of
`A_arc` or of the fixed-`j` bound `(j+1)log pi` would require the actual
archimedean possible-image hull to fill the corresponding container in the
radial direction (component length of order `pi` / `pi^{j+1}` for all relevant
copies) up to the normalized angular maximum.  The E_j skeleton supplies:

- no actual possible-image set;
- no theta values/theta function on `E_j`;
- no tensor-packet/procession weights or archimedean action;
- no proof that the container is sharp;
- no actual `C_F/C_K` equations or archimedean embeddings.

So the correct statement is only

```text
h_inf <= A_arc (conditional upper bound),
attainment of A_arc: OPEN/MISSING.
```

The IV container bound is not an equality theorem; `B_I` has zero normalized
log-volume, and the actual image can be a strict subset of the container.

## 8. Exact / conditional / missing

### Actual

- E_j equation, `j0=1/p^6`, discriminant, `v_p(Delta)=6`, local I_6, actual
  `q=p^6+744p^12+O(p^18)`, `qhat=pi^3 v` with unit `v`;
- `F=Q(i,E[6],F_sem)` contains `i`; hence every archimedean place of `F` is
  complex (`d_v=2`, `F_v~=C`), and `alpha_v=2/[F:Q]` with sum 1;
- `K=F(E[41])` formal Galois; `C_K/C_F/V/epsilon` formal source-level
  definitions;
- B_I-zero normalization: radial readout `log r`, angular term retained;
  shell log-volume `pi` is positive; `h_inf<=log pi` under shell containment.

### Conditional

- `K_v e=41,f=1`, explicit `F/K` and `E[41]` field data, `C_F/C_K` equations;
- IV container inclusion and hence `A_arc` upper bound;
- shell containment branch;
- actual `F_sem`, bad set, mod-41 image, complete C skeleton;
- any use of E_j complex periods as an archimedean input (not source-defined).

### Missing

- explicit archimedean embeddings of `F`/`K`;
- actual archimedean Θ-pilot possible-image set/hull `H_C,inf`;
- radial `r_v` and angular region/term;
- actual tensor-packet/procession archimedean data;
- positive lower bound `h_inf>=D`;
- container-attainment proof;
- complete C, TC-A..TC-H, TC-S, global `h_C>=Q_C`.

## 9. Conclusion

The E_j skeleton is a finite/local curve-and-field skeleton, not an
archimedean Θ-pilot construction.  It proves useful structural facts (all
archimedean places complex; weights `2/[F:Q]`; finite b=3 local data), but it
does not yield an actual `r_inf` or angular term.  The only archimedean
statement available is the conditional IV upper bound
`h_inf <= A_arc = 11.5 log pi = 13.164394...`, plus the weaker conditional
shell bound `h_inf <= log pi`.  No lower bound `h_inf>=D`, no attainment of
the maximal container, and no actual complete-C archimedean hull is obtained.

This is not a new attack and introduces no arbitrary `r_v`.  `target_accepted=false`;
full C9/P6 remains open.

## 10. Sources

- `C9-EJ-COMPLETION-20261025.md` (task-198) and `C9-AUDIT-EJ-20261025.md`
  (task-199) for the E_j/local/field skeleton and its missing/conditional data.
- `C9-GLOBAL-ASSEMBLY-BINDING-20261025.md` (task-185) and
  `C9-NORMALIZATION-DECISION-20261025.md` (task-182) for B_I-zero, radial
  readout, shell bound, container bound A_arc.
- `C9-AUDIT-NORMALIZATION-DECISION-20261025.md` (task-186) for the B_I-zero
  audit and the no-pi radius correction.
- IUT IV Prop1.5(iii)/Thm1.10(vii): `B_I`, `pi^{j+1}B_I`, `(j+1)log pi`,
  procession bound `((l+5)/4)log pi`.
- AbsTopIII Prop5.7(ii), Prop5.8(vi): unit-ball normalization, angular volume
  `2 pi`, shell log-volume `log pi`.
- IUT III Remark1.2.2(ii): archimedean shell radius `pi`.

End of C9-ARCH-ACTUAL-RINF-20261025.