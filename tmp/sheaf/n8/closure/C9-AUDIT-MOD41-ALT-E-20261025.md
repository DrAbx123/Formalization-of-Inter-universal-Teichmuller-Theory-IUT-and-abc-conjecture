# C9 audit: mod-41 image of the alternative E

Task: task-216. Date: 2026-10-25. Auditor: transport.
Stage: independent exact-computation/group-theory audit. No Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-MOD41-ALT-E-20261025.md | 166 | EB8CD3705E46AA800F99E14C974FF0EF70FB3E38F62D3CE44C22A8F044C70971 |
| C9-MOD41-IMAGE-20261025.md (prior E_j computation) | 201 | 993DE815B8442E2F44CC39877E597F7BD474180234EABE5EF4AE27DF25BBF21F |

## 1. Verdict

MOD41_ALT_E_AUDIT = MOSTLY VALID FOR SL2 CONTAINMENT; H=GL2 IS AN
OVERCLAIM; F-DEGREE IS CONDITIONAL.

Confirmed actual:

- discriminant factorization and v_p(Delta)=1 at p=12301;
- #E(F7)=10, a_7=-2;
- charpoly x^2+2x+7, discriminant 17 nonsquare in F41;
- the l=7 Frobenius element is irreducible;
- the order-41 unipotent from I1 gives an element of order 41 in the
  mod-41 image;
- the Dickson argument for **SL2(F41) subset image** can be made valid.

Error/overclaim:

- The conclusion image = GL2(F41) is NOT proved. The Dickson list used in the
  file omits the maximal subgroups that contain SL2 (e.g. SL2(F41) itself).
  H=SL2(F41) is a proper subgroup containing both the order-41 unipotent and
  the irreducible l=7 element, and is not contained in a Borel, Cartan
  normalizer, or exceptional subgroup. The file's statement "a proper
  subgroup must be contained in one of these four types" is false.
- The claimed exceptional orders as "projective order times scalar center
  order" are not the exact maximal subgroup orders for GL2(F41); the actual
  binary polyhedral maximal subgroups have orders 24, 48, 120 (or their scalar
  preimages 480, 960, 2400). All are 41-free, so the order-41 exclusion still
  works, but the order list is imprecise.
- The F-degree argument is conditional: F2 semistabilization degree 24 and
  F/Q Galois are asserted, not proved; other bad primes 19,12301,686229757
  are not included in F2. If F2 is not Galois, the Galois closure can introduce
  primes other than 2,3.

## 2. Exact arithmetic checks

### 2.1 Discriminant

For E: y^2=x^3+4x-2437249,

    Delta = -16(4*4^3 + 27*2437249^2)
          = -2566158921220528
          = -2^4 * 19 * 12301 * 686229757.

I verified this factorization. v_{12301}(Delta)=1, and the model has
A=4, B=-2437249 integral at 12301, with p=12301>=5. Hence the model is
minimal at p; v_p(j)=-1<0, so the reduction is multiplicative type I1.
VALID (conditional only on the standard minimal-model/Tate input).

### 2.2 l=7 point count

Modulo 7, B=-2437249 ≡ 4 (checked: -2437249 mod 7 = 4). The curve is

    y^2=x^3+4x+4 over F7.

Exact enumeration:

    x:            0  1  2  3  4  5  6
    f(x) mod 7:   4  2  6  1  0  2  6
    #y:           2  2  0  2  1  2  0

    #E(F7)=1+9=10,
    a_7=7+1-10=-2.

VALID.

### 2.3 Characteristic polynomial and discriminant

    x^2 - a_7 x + 7 = x^2 + 2x + 7 mod41,
    disc = 2^2 - 4*7 = -24 = 17 mod41.
    17^20 = 40 = -1 mod41,

so 17 is a nonsquare and the polynomial is irreducible over F41. VALID.

The other point counts in the table were independently spot-checked:
l=5 #=8, l=11 #=15, l=13 #=15, l=23 #=20, l=29 #=25, l=43 #=34, l=71 #=74;
the listed a_l and discriminants agree. These are not used in the conclusion.

## 3. Order-41 unipotent from I1

At p=12301 the reduction is multiplicative type I1. Standard Tate
uniformization: inertia acts on the l-adic Tate module by a unipotent matrix;
mod l=41 the generator reduces to a nontrivial unipotent element of order 41
in GL2(F41). The file does not compute q or the local matrix explicitly, but
this is a standard exact local fact. VALID CONDITIONAL on the Tate/I1 input.

Thus the mod-41 image H contains an order-41 unipotent.

## 4. Dickson argument: SL2 valid, GL2 invalid

### 4.1 The valid part: SL2 containment

Let H be the image in GL2(F41). H contains:

- the order-41 unipotent u;
- the irreducible Frobenius g.

Suppose H did not contain SL2(F41). By Dickson's classification, H is
contained in a maximal subgroup of GL2(F41) that does not contain SL2. Such
maximal subgroups are of the following types (indices/orders relevant here):

| type | order | 41 divides? |
|---|---:|---|
| Borel | 65600 = 41*40^2 | yes |
| split Cartan normalizer | 3200 = 2*40^2 | no |
| nonsplit Cartan normalizer | 3360 = 2*(41^2-1) | no |
| exceptional (binary A4/S4/A5 or scalar preimages) | 24,48,120 or 480,960,2400 | no |

All non-Borel types have order prime to 41, so H with its order-41 element
cannot be contained in them. Hence H would be contained in a Borel. But a
Borel subgroup is upper-triangular, so every element has an F41-eigenvalue;
the irreducible g is not in any Borel. Contradiction.

Therefore

    SL2(F_41) subset H.                                      (4.1)

This part is VALID.

### 4.2 The invalid part: H=GL2

The file concludes H=GL2. That does not follow. The classification of
**proper maximal subgroups of GL2** includes the subgroups containing SL2,
notably SL2(F41) itself (and possibly scalar/determinant preimages). The four
types listed by the file are exactly the maximal subgroups **not containing
SL2**; they do not exhaust proper subgroups.

Explicit counterexample to the file's reasoning:

    H = SL2(F_41)

is a proper subgroup of GL2(F41). It contains order-41 unipotents and
elements with irreducible characteristic polynomial. It is not contained in a
Borel (no common eigenline), not in a split/nonsplit Cartan normalizer (its
projective image is PSL2, not dihedral), and not in an exceptional subgroup.
Yet H != GL2.

Therefore:

    H = GL2(F_41) is NOT proved by the displayed data.

Correct conclusions:

    SL2(F_41) subset H subset GL2(F_41),
    H may be SL2 or a larger subgroup,
    determinant image and exact H are not determined.

### 4.3 Exceptional order imprecision

The file says "exceptional A4/S4/A5 projective orders 12/24/60, times scalar
center order divides 40", giving orders up to 2400. The actual maximal
subgroups in GL2 can be binary polyhedral groups of orders 24, 48, 120, and
their scalar preimages of orders 480, 960, 2400. The exact list depends on
which maximal subgroups are used, but every listed order is prime to 41, so
the exclusion via the order-41 element is unaffected. This is an imprecision,
not a fatal error for SL2 containment.

## 5. F=Q(zeta12,E[6],F2) degree

The arithmetic product is

    4 * 288 * 24 = 27648 = 2^10 * 3^3,

and 41 does not divide 27648. If the degree divides this product, then
41 is prime to [F:Q]. VALID ARITHMETIC.

However the degree argument has missing conditions:

1. E[6] splitting field degree divides |GL2(Z/6)|=288: valid.
2. [Q(zeta12):Q]=4: valid.
3. F2 semistabilization degree divides 24: asserted, not proved.
4. F/Q Galois: zeta12 and E[6] are Galois, but a semistabilization extension
   F2 need not be Galois. If F2 is not Galois, its Galois closure can have
   degree with primes other than 2,3; the product 27648 does not control the
   Galois closure.
5. F2 covers only the 2-adic part. The other bad primes 19,12301,686229757
   would require separate semistabilization; the file itself notes this, but
   the field F=Q(zeta12,E[6],F2) is then not the full semistable field needed
   for IUT I Def3.1.

Therefore the field-degree claim is CONDITIONAL/MISSING. It is not enough to
multiply 4*288*24; one must prove F2 is Galois of 2,3-power degree and add the
other bad-prime semistabilization degrees (or prove they are 2,3-smooth and
Galois).

## 6. Circularity check

- The order-41 unipotent and irreducible element are actual source data, not
  assumed surjectivity.
- The Dickson exclusion for SL2 uses only these elements and standard
  maximal-subgroup classification; no circular assumption.
- The H=GL2 conclusion is invalid because the maximal-subgroup list is
  incomplete, not because of circularity.
- The F-degree passage depends on the semistabilization/Galois input; it is
  conditional, not circular.

## 7. Exact classification

| item | status |
|---|---|
| Delta factorization, v_p(Delta)=1, I1 at 12301 | VALID |
| #E(F7)=10, a_7=-2 | VALID |
| charpoly x^2+2x+7, disc 17 nonsquare | VALID |
| l=7 Frobenius irreducible | VALID |
| order-41 unipotent from I1 | VALID CONDITIONAL on Tate/I1 |
| Dickson maximal groups not containing SL2 orders | MOSTLY VALID; exceptional orders imprecise |
| order-41 excludes split/nonsplit/exceptional | VALID |
| Borel excluded by irreducible element | VALID |
| SL2(F41) subset H | VALID |
| H=GL2(F41) | INVALID/OVERCLAIM |
| F-degree 4*288*24 arithmetic | VALID |
| F2 degree24 and F/Q Galois | CONDITIONAL/MISSING |
| other bad-prime semistabilization | MISSING |
| complete C/target | MISSING |

## 8. Corrected conclusion

For E: y^2=x^3+4x-2437249, the mod-41 image H satisfies

    SL2(F_41) subset H subset GL2(F_41).

The displayed data do not prove H=GL2; H could be SL2 or a larger subgroup.
The desired Def3.1(c) condition SL2(F41) subset H is met, conditionally on
the standard I1/Tate input. The exact H and determinant image over Q are not
determined.

Over F=Q(zeta12,E[6],F2), the index/degree passage to F remains conditional on
F2 being Galois of 2,3-power degree and on the other bad-prime semistabilization
degrees being 2,3-smooth and compatible; the arithmetic 27648 is not a proof of
those hypotheses.

No complete C or target conclusion follows.

target_accepted=false.
