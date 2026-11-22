# C9 P6NORM q-value: canonical -|log q| = -(b/41)log p

Task: task-390. Owner: kummer. Date: 2026-10-25.
Short theorem/proof or exact gap; no Lean/Project edits; no mixed/E3.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- sources/IUT-III.txt, 11456 lines, 566015 bytes,
  SHA256 822e03da7e2a7402a3bb406d698bb3374401e3fb102058c80864d6c06139353d.
- C9-P6NORM-A1-20261025.md (task-384), 244 lines,
  SHA256 1cf96545e696f6449f38d4a937f56e96a7c5d0b546e511492987d362eb253a2d.
- C9-COR312-IPL-20261025.md (task-372), 242 lines,
  SHA256 0c5fd9f3cefe18bfac2eeffe7f6494bca40f21c37dd8118faa6511af3b8b13cd.
- C9-TAME-LOG-DOMAIN-20261025.md, 251 lines,
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.
- C9-ARCH-NORMALIZATION-CORRECTION-20261025.md, 254 lines,
  SHA256 2174c3ee75fb9dfb83d1bc3e8ef43587f6fbf6d0a1d33538eecc6e0160c769f8.

## 1. Verdict

For the uniform C9 local profile at p=12301, e=41, b=3 or b=273:

    q_v = p^{2b} u,  u in 1+p^{2b}Z_p,
    qhat := q_v^{1/82} = pi^b v,  v in 1+pZ_p,  pi^41=p,
    -|log q| := -(1/82) v_p(q_v) log p
              = -v_p(qhat) log p
              = -(b/41) log p.                                (1.1)

The value is canonical: it is independent of u, v, and the choice of 82nd
root. The 82nd roots differ by mu_82; the q-pilot divisor/valuation is
unchanged, and root-of-unity factors have zero contribution to the normalized
log-volume.

Thus:

    b=3:   -|log q| = -(3/41) log 12301,
    b=273: -|log q| = -(273/41) log 12301.                        (1.2)

Exact gap: the numerical normalization -|log q| = -(1/82)v_p(q_v)log p is the
C9/TAME uniform-profile normalization. IUT III defines the q-pilot object and
its log-volume -|log q|, but does not state this local normalized formula as a
numerical theorem. The object-level definition plus the 82-root/valuation
normalization gives (1.1); the normalization convention is the only extra input,
and it is fixed, not arbitrary.

## 2. Local q_v and 82-root

For the E_j profile:

    q = p^{2b} u,  u in 1+p^{2b}Z_p,  v_p(q)=2b,
    qhat = q^{1/82} = pi^b v,  v in 1+pZ_p,
    qhat^82=q,  qhat^2=q^{1/41}=pi^{2b}.                        (2.1)

Since p=12301 does not divide 82, the 82nd-power map on 1+pZ_p is bijective;
v is unique for a fixed q. The 82nd roots of q form a mu_82-torsor:
qhat' = zeta qhat, zeta in mu_82 subset O_K^times.

Valuations:

    v_p(qhat)=v_p(q)/82 = 2b/82 = b/41,
    v_pi(qhat)=b,
    v_pi(q)=2b*41? No: v_pi(p)=41, so v_pi(p^{2b})=82b,
    q=pi^{82b}u.                                                  (2.2)

## 3. Normalized q-pilot value

Definition 3.8(i), IUT III lines 6506-6544, defines the q-pilot object as the
object of the global realified Frobenioid determined by the q_v at v in V_bad.
The q-pilot object is a divisor/line-bundle object; its log-volume is denoted
-|log q| (IUT III lines 858-916, 10682-10704).

The C9/TAME uniform-profile normalized log-volume of the q-pilot object at the
single bad p is the valuation normalization

    -|log q| = -(1/82) v_p(q_v) log p.                           (3.1)

Equivalently, using the 82-root qhat:

    -|log q| = -v_p(qhat) log p = -(b/41) log p.                  (3.2)

The unit u and the root-unit v do not enter: the q-pilot divisor is determined
by the valuation 2b, and the 82-root normalization divides that valuation by82.
The mu_82 root ambiguity changes qhat by a root of unity, which has the same
valuation and zero normalized log-volume contribution; so the value is
canonical.

For b=3: -|log q| = -(3/41)log12301.
For b=273: -|log q| = -(273/41)log12301.

These are the Q_p values used in the C9 profiles.

## 4. Why the unit/root ambiguity does not change the value

Let qhat' = zeta qhat, zeta^82=1. Then:

- v_p(qhat')=v_p(qhat);
- qhat'/qhat=zeta is a root of unity in O_K^times;
- multiplication by zeta preserves the q-pilot divisor valuation and the
  normalized log-volume; root-of-unity logarithms contribute zero.

Similarly, if q is replaced by q u with u in 1+p^{2b}Z_p (unit twist), then
qhat is replaced by qhat v with v in 1+pZ_p; the valuation of qhat is
unchanged. The q-pilot **divisor** is unchanged; the unit v has no zeros/poles
and does not change the q-pilot log-volume.

Thus the numerical value (1.1) is canonical despite the noncanonical qhat root
and the unit twist.

## 5. Exact gap: source normalization

IUT III defines:

- the q-pilot object as the object determined by q_v (Definition 3.8(i));
- its log-volume -|log q| (lines 858-916, 10682-10704);
- global arithmetic degrees as log-volumes (Proposition 3.9(iii)).

IUT III does not explicitly state the local normalized formula

    -|log q| = -(1/82) v_p(q_v) log p.

That formula is the C9/TAME uniform-profile normalization (B_I-zero/
procession-normalized readout), used to convert the q-pilot divisor at p into
the numerical scalar Q_p=-(b/41)logp. The derivation of (1.1) from q_v and the
82-root normalization is exact once that normalization is fixed; no arbitrary
choice of root or unit enters.

If one refuses the C9 normalization, the source gives only the q-pilot object
and the notation -|log q|, not its numerical value at p. This is the exact
remaining gap for A1/A3 no-black-box: the local normalization convention must
be recorded, not an arbitrary q or root.

## 6. What this fixes for A1/A3

A1 previously had q_v up to torsion and no numerical -|log q|. The present
theorem fixes:

    Q_p := -|log q| = -(b/41)log p,  b=3 or273,

with q_v=p^{2b}u, qhat=pi^b v, and the 82-root/valuation normalization. This
is the numerical q-pilot value needed for A1/A3.

What remains is not the q-value but:

- the fixed q-pilot F^{value x mu}-prime-strip/1-column representation
  (A1.2-A1.4, task-384);
- the determinant/localization/log-volume comparison A2;
- the fixed q-pilot value/SHE condition A3;
- the target normalization/translation to C9 Q_C/h_C.

## 7. Classification

| item | status |
|---|---|
| q_v=p^{2b}u, v_p(q_v)=2b | ACTUAL local E_j/q |
| 82-root qhat=pi^b v, v_p(qhat)=b/41 | ACTUAL local algebra |
| mu_82 root ambiguity | ACTUAL/root-of-unity action |
| -|log q| = -(1/82)v_p(q_v)logp = -(b/41)logp | PROVED under C9 normalization |
| independence of u and root choice | PROVED |
| b=3 value -(3/41)log12301 | PROVED |
| b=273 value -(273/41)log12301 | PROVED |
| source IUT numerical normalization | NOT STATED; C9 normalization input |
| A1/A3 numerical q-pilot value | FIXED conditional on C9 normalization |

## 8. Conclusion

The canonical q-pilot numerical value is

    -|log q| = -(b/41)log p,

derived from q_v=p^{2b}u, qhat=q_v^{1/82}=pi^b v, and the 82-root/valuation
normalization. It is independent of the unit u and the mu_82 root choice. For
b=3 this is -(3/41)log12301; for b=273 it is -(273/41)log12301. The only gap is
that the local normalized formula is the C9/TAME normalization, not an explicit
IUT III numerical theorem; the q-pilot object-level definition is source-level.
No arbitrary q/root is chosen; no mixed/E3 profile is used.

No Lean/kernel closure; target_accepted=false; P6 open.

## 9. Status

- Short natural-language theorem/exact-gap note only; no Lean/Project edits.
- Canonical q-pilot value fixed conditional on C9 normalization; exact source
  normalization gap recorded.
- target_accepted=false.
