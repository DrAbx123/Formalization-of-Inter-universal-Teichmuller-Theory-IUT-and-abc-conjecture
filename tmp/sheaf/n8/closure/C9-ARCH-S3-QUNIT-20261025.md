# C9 h_inf >= -S3 via qUnit / global section

Task: task-283. Date: 2026-10-25. Author: transport.
Short theorem/proof; new angle and exact obstruction. No arbitrary point/r_v.
No Lean/Project edits. Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-ARCH-LOWER-S3-20261025.md | 162 | 3847F1DEE3F3F73322A2F5F74E5ECC936E3FF0113BA3319FF76EA1D20904F73F |
| C9-ARCH-ACTUAL-RINF-20261025.md | 319 | 6AC23B85163E11706F8E26D96671437D8CFE80953FE5BA535BBA92FD5B15F236 |
| C9-ARCH-GLOBAL-20261025.md | 197 | 524E078AD85C72067627F006D165A724436E1BA508E86475C5F991860586E489 |

## 1. Verdict

The qUnit/global-section angle does NOT prove h_inf>=-S3 in the frozen source.

What is true conditionally:

- qUnit is a local element at the bad prime p; it has p-adic absolute value <1,
  and on the p-adic side its normalized qLog is negative.
- IF there were a global nonzero section s of a metrized q-pilot/Theta line
  with local component qUnit at p and unit local components at all other finite
  places, THEN the product formula would force the archimedean component of s
  to have modulus p^6 (or more generally the reciprocal of the finite
  valuations). If that arch component lies in H_C,inf, then a positive lower
  bound h_inf>=6 log p >> -S3 would follow.

But this conditional has two missing source objects:

1. no global section of the q-pilot/Theta line with the prescribed local
   components is constructed; qUnit is only a local completion element;
2. no theorem places the archimedean component of such a section in the actual
   theta-pilot hull H_C,inf.

Moreover, even a point in the hull gives a point-modulus bound, not a
hull-volume lower bound in the nonradial case. Therefore the qUnit route is
obstructed, not proved.

## 2. What qUnit actually is

At the bad prime p=12301, the paper q candidate gives

    qAtPrime S = q S in CommonPrimeCompletion (placeAtPrime S),
    qUnit S = Units.mk0 (qAtPrime S) ...,
    qLog = Real.log ||qUnit S||_norm < 0.                      (2.1)

The actual local q (for the E_j unit-twist profile) is

    q = p^6 + 744 p^12 + O(p^18),  v_p(q)=6,
    qUnit is a local p-adic unit, not an element of the global number field F.

It has no canonical archimedean component: qUnit lives at the chosen bad place
only. There is no map qUnit -> F or qUnit -> H_C,inf. The q-pilot line is a
local/native object; the frozen source does not construct a global section
whose local component is qUnit.

## 3. Conditional global-section theorem

Theorem 3.1 (hypothetical qUnit section). Assume:

(G1) a nonzero global section s of the metrized q-pilot/Theta line on the
     arithmetic curve C;

(G2) at p, s has local component qUnit, and at all finite places v!=p, the
     local component of s is a unit (valuation0);

(G3) the archimedean component s_inf lies in the actual radial hull H_C,inf
     (or its modulus is at most the hull radius r_inf).

Then

    log||s_inf||_arch = 6 log p,                              (3.1)
    h_inf >= 6 log p > 0 >= -S3.                              (3.2)

Proof. Product formula for the global section:

    sum_p alpha_p v_p(s) log p + sum_{v|infty} alpha_v log||s||_v =0.

With v_p(s)=6 and all other finite valuations0, the archimedean sum is
-6log p; for a single real place this gives log||s_inf||=6logp. If s_inf is in
the radial hull, r_inf>=||s_inf||, hence h_inf>=log r_inf>=6logp. QED.

This is a valid conditional theorem, much stronger than needed. It is not an
actual source theorem:

- G1 is not constructed;
- G2 is not a property of the local qUnit; it is a choice/section hypothesis;
- G3 requires membership in the actual archimedean hull, which is missing.

## 4. Why the local qUnit does not suffice

### 4.1 No global section

The product formula applies only to a global section/element. qUnit is a local
completion element at p; there is no canonical global element with prescribed
qUnit local component. Constructing one would require a global q-pilot section
with specified local behavior at p and units elsewhere, which is not in the
frozen source. The native q-pilot line may not have such a section at all.

### 4.2 No archimedean membership

Even if a global section s with local qUnit at p existed, its archimedean
component would be determined by the product formula, but there is no theorem
that this component is a possible image of the Θ-pilot or lies in H_C,inf.
The target hull is constructed from actual Θ-pilot possible images, not from
an arbitrary q-pilot section. Assigning s_inf to H_C,inf would be an arbitrary
point choice.

### 4.3 Point versus hull volume

If s_inf is a point of modulus r, radial hull containment gives r_inf>=r and
h_inf>=log r. But for a nonradial hull, the angular term matters; a point gives
only a point-modulus constraint, not a full volume bound. The source does not
prove the archimedean hull is a radial ball of radius r_inf. Thus even a
constructed point would not automatically give h_inf>=-S3 in the nonradial
case; an actual region/ball is needed.

### 4.4 Sign check

qUnit has p-adic norm <1, so its finite valuation is positive; a global section
would have positive arch norm, not negative. The product formula would give a
positive lower bound, which is stronger than -S3. This does not make the
argument valid; the missing global section is essential.

## 5. Exact obstruction

There is no source-valid qUnit/global-section proof of h_inf>=-S3 because:

(O1) qUnit is local, not a global section; no q-pilot/Theta global section with
     prescribed local qUnit and unit elsewhere is constructed;
(O2) no theorem places the archimedean component of such a section in H_C,inf;
(O3) even a point in H_C,inf gives only a point-modulus bound; the nonradial
     angular term and hull volume are not controlled;
(O4) the actual archimedean possible-image set/H_C,inf remains missing
     (task-232), so there is no actual hull to which G3 can refer.

Therefore the qUnit route proves only the conditional Theorem 3.1. It does not
prove h_inf>=-S3 and does not close the b=3 B=I corridor.

## 6. What would make the route work

A genuine source construction would need at least:

1. a canonical global q-pilot/Theta section with local component qUnit at p and
   controlled finite/arch components (not an arbitrary section);
2. a proof that its archimedean component/region lies in the actual Θ-pilot
   hull H_C,inf;
3. a radial-hull or full angular/volume computation to convert the point bound
   into h_inf>=-S3.

None is present in the frozen source. Absent these, the qUnit/global-section
angle is an obstruction, not a proof.

## 7. Conclusion

The qUnit/global-section attack does not give h_inf>=-S3. Conditionally, a
global q-pilot section with local qUnit at p, units elsewhere, and archimedean
component in H_C,inf would give the much stronger bound h_inf>=6log p>0. But the
global section, its archimedean membership, and the radial/volume control are
all missing; qUnit itself is local and has no arch component.

Exact obstruction: O1-O4. No arbitrary point or r_v was chosen. P6 remains
open; the b=3 B=I corridor is not closed by this route.

target_accepted=false.
