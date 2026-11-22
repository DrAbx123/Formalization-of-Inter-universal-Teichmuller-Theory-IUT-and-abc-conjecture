# C9 archimedean lower bound h_inf >= -S3

Task: task-270. Date: 2026-10-25. Author: transport.
Short theorem/proof and obstruction. No arbitrary r_v; no Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-ARCH-ACTUAL-RINF-20261025.md (task-232) | 319 | 6AC23B85163E11706F8E26D96671437D8CFE80953FE5BA535BBA92FD5B15F236 |
| C9-NEW-VARIATIONAL-COUNTEREXAMPLE-20261025.md | 157 | 100AF6DF5D98B850E1F13D9E259EF360E7D1B70B64F3C7753A038EBAFC3DCBA3 |
| C9-GLOBAL-ASSEMBLY-BINDING-20261025.md | 271 | 0888F47DC5D5DC21410F39FF7A81D4315E55FABD84E882BC3D17FDB27A25D9FA |

Convention: B_I-zero normalization, F=Q-h, P6 is h>=Q (F<=0).
For b=3 B=I:

    S3=(12/41)log 12301=2.7563226845469613...,
    F=-S3-h_inf,
    F<0  <=> h_inf>-S3,
    F>=0 <=> h_inf<=-S3.                                      (0.1)

Closing the b=3 B=I counterexample corridor requires the lower bound
h_inf>=-S3. This note proves that bound conditionally and proves that the
candidate source mechanisms do not give it in the frozen corpus.

## 1. Verdict

The bound h_inf>=-S3 is NOT proved from the current source.

The available structural facts are:

- B_I-zero normalization: logvolume(B_I)=0;
- IV container: H_C,inf subset pi^{j+1}B_I and h_inf<=A_proc=13.164393...;
- product formula for points, not for the hull volume;
- no actual archimedean possible-image hull H_C,inf;
- no global point x with a proved membership x in H_C,inf.

The direction of the IV container is **opposite** to what a lower bound would
need: H_C,inf is contained in the container, not the container in H_C,inf.
Product formula gives point-modulus constraints, not a positive hull-volume
lower bound. Therefore no source theorem gives h_inf>=-S3.

The exact missing input is either:

(A) a containment B_I subset H_C,inf (which would imply h_inf>=0), or
(B) a global point x in H_C,inf with finite valuation sum <=S3 (which would
    imply h_inf>=-S3 by product formula), or
(C) a direct lower bound on the actual archimedean hull volume.

None is supplied. No arbitrary r_v is chosen.

## 2. Conditional mechanisms

### 2.1 If B_I subset H_C,inf, then h_inf>=0

Under B_I-zero, logvolume(B_I)=0. If the actual archimedean hull contains the
unit ball B_I, monotonicity of the normalized volume gives

    h_inf >= logvolume(B_I)=0 >= -S3.                          (2.1)

This is a valid conditional implication. Its hypothesis is not a source
theorem. In fact IV gives the opposite container inclusion
H_C,inf subset pi^{j+1}B_I, not B_I subset H_C,inf. The latter would be a
strong positivity statement: the possible Θ-pilot images fill a unit ball.
No such statement appears in IUT III/IV or in the E_j skeleton.

### 2.2 If a global unit lies in H_C,inf, then h_inf>=0

Let x in F^times be a global unit with x in the radial hull H_C,inf. Product
formula gives

    sum_v alpha_v log|x|_v + sum_p alpha_p v_p(x) log p=0,
    v_p(x)=0 all p  =>  sum_v alpha_v log|x|_v=0.             (2.2)

Since x is in the hull, r_v>=|x|_v, so

    h_inf >= sum_v alpha_v log|x|_v =0 >= -S3.                  (2.3)

Again conditional. No theorem identifies a global unit (e.g. 1 or a root of
unity) with a point of the actual Θ-pilot hull H_C,inf. The IUT possible-image
hull is not the set of curve points or field units; E_j supplies no map from
F^times to H_C,inf.

### 2.3 If a global point with small finite valuation lies in H_C,inf

For general x in F^times with x in the radial hull,

    h_inf >= -sum_p alpha_p v_p(x) log p.                      (2.4)

Thus h_inf>=-S3 follows if

    sum_p alpha_p v_p(x) log p <= S3.                          (2.5)

For a global unit this is 0<=S3, recovering 2.2. For finite-integral x all
valuations are nonnegative and the left side is >=0, so (2.5) is not automatic;
for x=1 it is zero. If x has denominator at a bad prime, the left side may be
positive and can exceed S3; then product formula gives a weaker bound.

No actual x in H_C,inf is constructed, and no source theorem gives (2.5) for a
canonical x. The product formula alone is only a point constraint; it does not
give a hull-volume lower bound for an arbitrary archimedean region.

### 2.4 Container cannot give a lower bound

IV gives

    H_C,inf subset pi^{j+1}B_I,  h_inf <= (j+1)log pi,          (2.6)

and after procession average h_inf<=A_proc. These are upper bounds. They are
compatible with h_inf arbitrarily negative (a tiny possible-image set inside
the container). Therefore they cannot imply h_inf>=-S3.

## 3. Obstruction theorem

Theorem 3.1 (exact obstruction). The frozen source does not prove any of:

(i) B_I subset H_C,inf;
(ii) existence of a global unit in H_C,inf;
(iii) existence of a global point x in H_C,inf with finite valuation sum <=S3;
(iv) a direct hull lower bound h_inf>=-S3.

Consequently h_inf>=-S3 is not available, and the b=3 B=I corridor remains
undecided.

Proof. Task-232 establishes that the actual archimedean Θ-pilot
possible-image set and H_C,inf are not constructed; only the IV upper container
and the B_I-zero formal normalization are available. The E_j skeleton has no
map to H_C,inf and no actual archimedean points. IUT III/IV give containment
H_C,inf subset container, not the reverse; they do not identify a global
point/unit in H_C,inf. Product formula applies only to points known to be in
the hull. Therefore none of (i)-(iv) follows. QED.

Corollary 3.2. No positivity of F for b=3 B=I is proved; and no closure of the
b=3 B=I corridor follows. The sign of F=-S3-h_inf remains unknown.

## 4. What would prove the bound

A genuine source proof of h_inf>=-S3 could proceed by one of:

1. Constructing an actual global point x (canonical, not arbitrary) in the
   image of the Θ-pilot archimedean possible-image set with finite valuation
   sum <=S3. The natural candidate is a global unit/torsion point of norm 1,
   but membership in H_C,inf must be proved.
2. Proving B_I subset H_C,inf (or a large ball of radius exp(-S3)) from the
   actual Θ-pilot values. This is a lower volume/sharpness statement, not the
   IV upper container.
3. Constructing H_C,inf itself and computing its normalized volume directly.

None is in the frozen source. Any of 1-3 would be a new source theorem, not a
formal consequence of the current B_I-zero container or product formula.

## 5. Conclusion

The requested lower bound h_inf>=-S3 is not proved. B_I-zero and the IV
container give only h_inf<=A_proc; product formula gives conditional point
bounds only if a point is known to lie in the hull; no global unit/torsion
point or B_I containment in H_C,inf is constructed. The exact obstruction is
the absence of (i)-(iv). Therefore the b=3 B=I corridor remains conditional
and no P6 conclusion follows.

No arbitrary r_v or point was chosen. target_accepted=false.
