# C9 C1 domain correction: LGP action on VC(I)

Task: task-452. Owner: multiradial. Date: 2026-10-25.
Rigorous source/domain audit only. No Lean/Project edits; no mixed/E3; no
arbitrary data. Deliverable: this file only. target_accepted=false; C1/P6 open.

## 0. Audited statement D1

D1 as used in the C1 log-shell/volume routes:

    On VC(I), the map
        S |-> 1*S = LGP*S
    is defined (as a self-map of VC(I)); determine whether it is
    injective/surjective, measurable, and has constant Haar Jacobian.
    Also determine whether LGP^{-1}S_q lies in VC(I).

Here VC(I) is the large log-shell volume container of LANA 5.2; LGP is the
LGP element of 5.2(f); S_q is the q-pilot diagonal region S_q={q_v O_v}
embedded diagonally in the large volume container.

Verdict:
  - D1 is NOT a source-defined self-map of VC(I). LGP belongs to VC(O), and
    VC(K) is a VC(O)-module, but VC(I) is not a VC(O)-module. The source only
    asserts LGP*U subset VC(I) tensor_Z Q for U subset VC(I) (LANA 6.2(i),
    line 2088); the codomain is the rationalized container, not VC(I).
  - On VC(K)/VC(O), multiplication by LGP is defined. On VC(K) it is bijective
    (componentwise by nonzero LGP_v); on VC(O) it is injective but generally
    not surjective (LGP is a nonunit at bad places). It is continuous/
    measurable and has a constant Haar scaling factor on these spaces.
  - On VC(I) there is no Haar self-map/Jacobian statement, because the map
    lands in VC(I) tensor Q, where the finite Haar normalization does not
    exist.
  - LGP^{-1}S_q is generally NOT in VC(I): LGP^{-1} has negative p-adic
    valuations at bad places, and the product with S_q leaves the log-shell
    integral structure for j>=2. No source theorem places it in VC(I).

## 1. Exact source definitions

LANA 5.2(d)-(f), extracted text lines 1618-1650:

  - VC(K) is naturally a VC(O)-module (line 1618);
  - volume normalization: vol(VC(O))=1, multiplication by p_v at v acts as
    p_v^{-1} on the volume; log-vol(S)=log vol(S) (lines 1621-1627);
  - LGP in VC(O), LGP=(LGP_v) for v in V, and for v bad
        LGP_{S_{j+1},v} = (tensor_{t in S_j} 1_{w|vQ}) tensor q_v^{j^2},
    for v good the corresponding factor is 1 (lines 1630-1650).
  Here q_v is the 2l-th root of the q-parameter fixed in LANA 4.2(c); it is
  integral at v bad (positive valuation) but not a unit. Hence LGP is an
  element of VC(O) that is nonunit at bad places.

LANA 6.2(i), lines 2085-2088:

  "When the local action of Step 7 is assembled globally ... the possible
   images of the Theta-pilot object are obtained as
        LGP*U subset VC(I) tensor_Z Q,
   where U ranges over suitable subsets of the large volume container VC(I)."

This is the exact source statement of the LGP action on subset regions:
  - U is a subset of VC(I);
  - LGP*U lies in the rationalization VC(I) tensor_Z Q;
  - it is NOT asserted that LGP*U lies in VC(I).
So D1's S |-> LGP*S is not a self-map of VC(I); it is a map from subsets of
VC(I) to subsets of VC(I) tensor Q, or a map on the rationalization, not a map
VC(I)->VC(I).

## 2. Is S |-> LGP*S defined on VC(I)?

### 2.1 As a self-map: NO

VC(I) is a product of log-shells I_v; it is a Z_p-module / additive
topological group, not a VC(O)-module. The element LGP in VC(O) acts on VC(K)
by multiplication using the VC(O)-module structure of VC(K) (line 1618). That
module structure does not pass to VC(I): I_v is not an O_v-module, and the
product LGP*S of an element of VC(O) and an arbitrary subset S of VC(I) is not
an internal operation of VC(I).

The source's exact assertion (line 2088) gives
    LGP*U subset VC(I) tensor_Z Q,
not LGP*U subset VC(I). Therefore D1 as a self-map of VC(I) is NOT DEFINED by
LANA.

### 2.2 On VC(K): defined

VC(K)=product_v LocVC(K)_v is a VC(O)-module. For S subset VC(K), LGP*S is
defined componentwise. LGP_v is nonzero at every v (bad component q_v^{j^2}
nonzero; good component 1; archimedean component nonzero in the LANA
normalization). Multiplication by a nonzero element of the product of local
fields is componentwise bijective on VC(K) (inverse 1/LGP_v exists in K_v,
though not necessarily in O_v). Thus on VC(K):
    LGP* : VC(K) -> VC(K) is a bijection.
But VC(K) has infinite Haar measure at archimedean/noncompact factors and is
not the finite-measure space used in the volume lemma; this is not the D1
domain.

### 2.3 On VC(O): defined but not onto

Since LGP in VC(O) and VC(K) is a VC(O)-module, multiplication by LGP maps
VC(O) into VC(O). It is injective (componentwise nonzero). It is not
surjective in general: at a bad place, LGP_v contains q_v^{j^2}, a nonunit; an
arbitrary element of O_v is not divisible by q_v^{j^2} in O_v. So
    LGP* : VC(O)->VC(O) is injective, not surjective.
This is not D1 either, since D1 is stated on VC(I).

### 2.4 On the rationalization VC(I) tensor Q

The source's LGP*U lives in VC(I) tensor_Z Q. On this rational vector space,
multiplication by LGP is a bijection because LGP is nonzero in the product of
fields (inverse includes denominators, allowed after tensor Q). But
VC(I) tensor Q is not compact and has no finite Haar measure normalized as in
LANA 5.2(e). The finite-volume measure/non-atomic arguments of the volume lemma
do not apply to this rationalization.

Conclusion for definedness:
  - D1 as stated on VC(I) is NOT a source-defined self-map; it is only
    defined after passing to VC(I) tensor Q.
  - If extended to VC(I) tensor Q, it is bijective, but the finite Haar
    normalization and the volume-range lemma are lost.

## 3. Injective/surjective

On the actual source domain/codomain:

  - VC(K): multiplication by nonzero LGP is bijective (componentwise nonzero
    field elements). This is a set-theoretic bijection, but VC(K) is not the
    finite-measure log-shell container and its Haar measure is infinite.
  - VC(O): multiplication by LGP is injective, not surjective (LGP nonunit at
    bad places).
  - VC(I): the map is not a self-map; injectivity/surjectivity of a
    VC(I)->VC(I) map is not defined. If one regards the map
    VC(I)->VC(I) tensor Q, it is injective but its image is not VC(I) (it is a
    coset/lattice translate in the rationalization).
  - VC(I) tensor Q: bijective.

D1's requested injective/surjective answer for VC(I) is therefore ILL-POSED/
NOT SOURCE-DEFINED; the only source-valid map is into the rationalization,
where it is bijective but not a finite-measure self-map.

## 4. Measurability

  - On VC(K)/VC(O), multiplication by the fixed element LGP is continuous
    (locally compact group/module), hence Borel measurable.
  - On VC(I) as a map to VC(I) tensor Q, one may define Borel measurability
    after choosing the rationalized Borel structure, but this is not
    measurability of a self-map of VC(I), and the target has no finite Haar
    measure.
  - The source's LGP action is a construction algorithm on possible regions
    subject to Ind1/Ind2 and upper semi-compatibility Ind3 (Theorem3.11;
    APT), not a global measurable self-map of VC(I). Treating it as a
    measurable bijection of VC(I) is an extra hypothesis (the APT conflict
    already noted in task-445/447).

Thus D1's "measurable self-map of VC(I)" is not source-supported.

## 5. Constant Haar Jacobian

On VC(K), multiplication by LGP is a product of local scalings; the Haar
measure scales by the constant

    J_K = product_{v in V} |LGP_v|_v

(assuming the local Haar normalizations are fixed; this is a product of
nonnegative local factors). On VC(O), the same constant scaling applies to the
restricted multiplication map (LGP in VC(O)); the Haar measure of LGP*S is
J_K*mu(S) for measurable S subset VC(O), provided the local scalings are
defined.

On VC(I), there is no self-map and hence no Haar Jacobian on VC(I). The
natural map VC(I)->VC(I) tensor Q has no finite Haar measure; a "constant
Jacobian" would be a scaling of the rationalized (infinite) Haar measure, not
the normalized volume of LANA 5.2(e). Therefore D1's "constant Haar Jacobian
on VC(I)" is NOT DEFINED/FALSE as stated.

If one restricts to VC(O) (where LGP acts), a constant Jacobian does exist,
but that is not the log-shell container D1 asks about. The constant is
J_K=product |LGP_v|_v, not necessarily 1; bad factors |q_v^{j^2}|_v are
nonunit (positive valuation), so J_K is not 1 in general.

## 6. Is LGP^{-1}S_q in VC(I)?

S_q={q_v O_v} is the q-pilot diagonal in the large volume container. LGP has
bad components q_v^{j^2}. Its inverse has components q_v^{-j^2}, which have
negative p-adic valuation at bad v. Multiplying S_q by LGP^{-1} produces
components with valuation proportional to (1-j^2) (after the q_v normalization),
negative for j>=2. Such elements are not in the integral log-shell I_v for all
j; they leave VC(I) and generally lie only in VC(K)/VC(I) tensor Q.

More precisely, even if q_v is chosen so that one component q_v^{-1}*q_vO_v
is integral, the higher j-components q_v^{-j^2}*q_vO_v have increasingly
negative valuations and are not in the compact log-shell I_v. No source
theorem asserts LGP^{-1}S_q subset VC(I). Therefore:

    LGP^{-1}S_q is NOT proved to be in VC(I); in general it is not.

This blocks the inverse-map version of the domain correction: one cannot move
S_q back into VC(I) by LGP^{-1} without leaving the log-shell container.

## 7. Verdict on D1

  (a) Defined on VC(I)? NO. LGP acts on VC(K) as a VC(O)-module and maps
      VC(I) regions into VC(I) tensor Q, not into VC(I). D1 as a self-map is
      not source-defined.
  (b) Injective/surjective? On VC(K): bijective; on VC(O): injective not
      surjective; on VC(I): ill-posed/not a self-map; on VC(I) tensor Q:
      bijective.
  (c) Measurable? On VC(K)/VC(O): continuous/measurable; on VC(I) as
      self-map: not defined; on VC(I)->VC(I) tensor Q: Borel but no finite
      Haar.
  (d) Constant Haar Jacobian? On VC(K)/VC(O): constant J_K=product |LGP_v|_v
      (generally not 1); on VC(I): undefined (no finite Haar self-map).
  (e) LGP^{-1}S_q in VC(I)? NOT proved; generally false, because inverse
      components have negative valuations outside the log-shell.

D1 is therefore REJECTED in the form "LGP acts as a measurable self-map of
VC(I) with constant Haar Jacobian." The source-valid statement is the local/
module action on VC(K)/VC(O) and the inclusion LGP*U subset VC(I) tensor Q.
Any use of D1 to build T_1:VC(I)->VC(I), invert it, or apply the finite-volume
lemma on VC(I) is an extra hypothesis, not a consequence of LANA/Theorem3.11.

## 8. Consequence for C1

The C1 log-shell/volume routes need a self-map of VC(I) (or an inverse) to
transport q-pilot regions and match classes. D1 shows the required self-map is
not source-defined: the LGP action naturally lands in the rationalization,
where the finite Haar normalization/measure-existence lemma does not apply;
the inverse generally leaves VC(I). Therefore:
  - T_1:VC(I)->VC(I) is not source-supported;
  - LGP^{-1}S_q in VC(I) is not established;
  - the measure-existence Lemma B on VC(I) cannot be applied to the image of
    LGP without an extra argument placing the image back in VC(I);
  - C1 remains open; the domain correction is not a technicality but a
    genuine source-domain obstruction.

No Lean/Project edits; no mixed/E3; no arbitrary LGP normalization or inverse
is assumed. target_accepted=false.

## 9. Acceptance

Only C9-C1-DOM-ACTION-20261025.md written. Natural-language source/domain
audit only; no Lean/Project/target edits; no independent review/kernel/
comparator run. target_accepted=false; C1/P6 open.
