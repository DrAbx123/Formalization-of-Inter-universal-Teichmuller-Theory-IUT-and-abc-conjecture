# C9 independent archimedean B_I possible-image audit

Task: task-368. Owner: qside. Date: 2026-10-25.
Natural-language theorem/audit and exact obstruction; no arbitrary data; no
mixed/E3 profiles; no Lean/Project/target edits; only this file written.

## 0. Verdict

Under the frozen IV/B_I-zero/Theta-pilot archimedean definitions, B_I is **not**
an actual Theta-pilot possible image and is **not** a target-hull factor.  It
is the reference unit ball used for the B_I-zero normalization.  The IV
container gives the opposite inclusion direction

    H_C,inf subset pi^{j+1} B_I,                                  (0.1)

not B_I subset H_C,inf.  Nothing in B_I-zero normalization, IV Prop1.5/Thm1.10,
or the Theta-pilot definitions asserts that B_I or a positive-radius ball is
contained in the actual archimedean possible-image hull.

Therefore h_inf>=0 is not proved, and the b=3 B=I P6 corridor is not reached.
The exact obstruction is the missing actual archimedean possible-image set
H_C,inf plus a lower/membership statement for B_I; the available IV data are
only upper bounds.

No arbitrary B_I point/ball is inserted.  No mixed/E3 profile is used.

## 1. Roles of the objects

### 1.1 B_I

B_I is the reference unit ball at an archimedean place under the binding
B_I-zero normalization:

    logvolume(B_I) = 0,
    h_v^rad(B_v(r_v)) = log r_v,
    h_inf = sum_{v|infty} alpha_v [ h_v^ang(A_v) + log r_v ].      (1.1)

It is a normalization/reference object.  B_I-zero fixes the zero of the
log-volume coordinate; it does not assert that B_I is a possible image, a hull
component, or a subset of the hull.

### 1.2 H_C,inf

H_C,inf is the actual archimedean component of the holomorphic hull of the
union of possible Theta-pilot images of the fixed complete C.  Its construction
requires:
- the actual archimedean possible-image set of the source Theta-pilot object;
- the archimedean places/embeddings and the angular regions A_v;
- the radial radii r_v and the hull operation.

Task-232 established that the E_j/F/K skeleton does not construct H_C,inf, its
radii r_v, or its angular terms; there is no map E_j(C)/periods -> H_C,inf.

### 1.3 IV container

IV Prop1.5(iii)(iv)/Thm1.10(vii) gives, for the length-pi shell,

    H_C,inf subset pi^{j+1} B_I,
    h_inf <= (j+1) log pi,
    h_inf <= A_arc = ((l+5)/4) log pi = 11.5 log pi = 13.164393687... .  (1.2)

This is an upper container.  Its inclusion direction is (0.1), opposite to the
lower/large-ball containment that h_inf>=0 would need.

## 2. Conditional B_I theorem

Theorem 2.1.  If B_I subset H_C,inf, then h_inf>=0.

Proof.  By B_I-zero, logvolume(B_I)=0.  Normalized log-volume is monotone
under inclusion, so

    h_inf = logvolume(H_C,inf) >= logvolume(B_I) = 0.              (2.1)

QED.

This is the only valid route from B_I to a lower bound.  Its hypothesis is not
a source theorem.  In fact (0.1) is the reverse containment: H_C,inf lies
inside a pi^{j+1}-scaled unit ball, not the other way around.

## 3. Why B_I is not an actual possible image

The possible images of the Theta-pilot object are the actual Theta/Gaussian
values and their tensor-packet regions, not the normalization ball B_I:

- the zero label/constant splitting produces a constant/unit factor, not an
  allowed Theta-pilot output equal to B_I;
- the identity action A^0 is an action identity, not an allowed pilot output
  (task-278);
- the source definitions give no map from the reference ball B_I to a
  possible-image set or to H_C,inf;
- B_I enters only in the normalization of log-volume and in the IV upper
  container.

Choosing B_I as a possible image or a hull factor would be an extra assumption,
not a source theorem.

## 4. Why B_I-zero does not imply membership

B_I-zero is a choice of reference volume:

    logvolume(B_I)=0.

It says nothing about whether B_I is contained in the actual possible-image
hull.  The hull H_C,inf may be a tiny subset of B_I (indeed IV permits this:
H_C,inf subset pi^{j+1}B_I for any j), or may have a larger log-volume.  The
normalization fixes the zero, not a lower bound.

## 5. Exact obstruction

The frozen source does not provide any of:

(i) an actual archimedean possible-image set for the Theta-pilot object;
(ii) the actual hull H_C,inf with its r_v and angular terms;
(iii) B_I subset H_C,inf or any positive-radius ball containment;
(iv) a global point/unit x in H_C,inf with controlled finite valuation sum;
(v) a direct lower bound h_inf>=0 from IV/B_I-zero.

Available only:
- B_I-zero normalization logvolume(B_I)=0;
- IV upper container H_C,inf subset pi^{j+1}B_I and h_inf<=A_arc;
- product formula as a pointwise identity for points already known to lie in
  the hull;
- E_j finite local data, which do not construct H_C,inf.

The IV direction is opposite to (iii); product formula needs a point (iv); the
B_I reference is not a possible image; and H_C,inf is not constructed.  Hence
none of (i)-(v) follows.

## 6. Consequence for b=3 P6

Conditional:
- If B_I subset H_C,inf, then h_inf>=0.  For the b=3 B=I branch,
  F=-S3-h_inf<0, so P6 holds for that conditional branch.
- For the b=3 B=O_K branch, h_inf>=0 would make F=D3-h_inf>0, i.e. it would
  not prove P6; it would strengthen the positive deficit.  Thus B_I containment
  is branch-sensitive and cannot be advertised as "b=3 P6" without specifying
  the B=I branch.

Actual:
- B_I subset H_C,inf is not proved.
- h_inf>=0 is not proved.
- The b=3 B=I corridor remains conditional on B_I subset H_C,inf (stronger than
  h_inf>=-S3) and on the actual B=I branch/kappa.

No arbitrary B_I ball, point, or radius is used.  No mixed/E3 profile is
inserted.

## 7. Classification

PROVED:
- B_I is the B_I-zero reference ball; logvolume(B_I)=0;
- IV gives H_C,inf subset pi^{j+1}B_I and h_inf<=A_arc (conditional on target
  containment);
- B_I subset H_C,inf => h_inf>=0 (monotonicity);
- B_I is not an actual Theta-pilot possible image in the frozen source;
- no source theorem gives B_I subset H_C,inf.

CONDITIONAL/MISSING:
- actual H_C,inf and its r_v/A_v;
- B_I membership in H_C,inf;
- h_inf>=0 and the b=3 B=I P6 conclusion;
- actual B=I branch/kappa, complete C.

WITHDRAWN:
- treating B_I as a possible image or target hull factor by definition;
- deriving B_I subset H_C,inf from IV, B_I-zero, or the target container;
- advertising h_inf>=0 as an unconditional b=3 P6 result.

## 8. Conclusion

B_I is a normalization reference, not an actual Theta-pilot possible image or
a target hull factor.  IV gives only the upper container
H_C,inf subset pi^{j+1}B_I, the opposite direction from B_I subset H_C,inf.
B_I-zero fixes logvolume(B_I)=0 but does not imply membership.  The conditional
theorem B_I subset H_C,inf => h_inf>=0 is valid, but its hypothesis is not in
the frozen source.  The exact obstruction is the missing actual archimedean
possible-image hull/membership; the b=3 B=I corridor remains conditional.

target_accepted=false; P6 open.

## 9. Sources

- C9-ARCH-ACTUAL-RINF-20261025.md (task-232): H_C,inf/r_v/angular missing;
  IV upper only.
- C9-ARCH-HULL-20261025.md (task-240): IV container direction and upper
  bound; B_I-zero normalization; large capsules outside target.
- C9-NORMALIZATION-DECISION-20261025.md / C9-GLOBAL-ASSEMBLY-BINDING-20261025.md:
  B_I-zero binding normalization.
- C9-ARCH-LOWER-S3-20261025.md, C9-ARCH-LOWER-NEW-20261025.md,
  C9-ARCH-S3-BIREGION-20261025.md: B_I containment conditional only; product
  formula pointwise; no global unit/point in hull.
- C9-B3-BI-CORRIDOR-20261025.md: conditional b=3 B=I P6 corridor and the
  distinction between kappa and h_inf.
