# C9 independent mixed-profile arch attack: no B_I/h_inf>=0 from mixed data

> **SCOPE CORRECTION (2026-10-25):** This file's mixed bad/good profiles (0<rho<1) are **NOT possible images of the fixed F_mod=Q uniform target**. IUT I Def3.1(e) V-section selects one place per rational p, so bad mass is rho in {0,1}; C9-GLOBAL §1 forbids replacing unselected conjugates by rho=1/2. Task-307 confirms mixed profiles are an E3 profile change. The mixed-profile P6 claims below are **PROFILE-CHANGE/CONDITIONAL only** and are **not usable for original P6**; no mixed P6 rescue, mixed counterexample, or mixed U refutation follows. Uniform-profile-only correction: C9-MIXED-PROFILE-CORRECTION-20261025.md.

Task: task-313. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits, no arbitrary r_v/region.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- C9-MIXED-ARCH-BI-20261025.md (task-311), 118 lines,
  SHA256 f2ae031bbdc7b8f2656541812f467f53ac55cbb820bcd8644bd962b1aeb613b5.
- C9-MIXED-VOLUME-EXACT-20261025.md (task-304), 212 lines,
  SHA256 0b5149c086a2518428059a018f85280084cf6c25c1cc8923f7f3a1c8f5f7e5d1.
- C9-MIXED-PROFILE-P6-20261025.md (task-305), 181 lines,
  SHA256 3fe775246c9147f35a116e0bbc409c9d4a2f9b26477c9f25ead9ec14b508f0c4.
- C9-ARCH-LOWER-S3-20261025.md (task-270), 163 lines,
  SHA256 3847f1dee3f3f73322a2f5f74e5ecc936e3ff0113ba3319ff76ea1d20904f73f.
- C9-TAME-LOG-DOMAIN-20261025.md, 251 lines,
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.

Setting: 0<rho<1 mixed all-bad profile, m(rho)=-(1/m)sum_j rho^{j+1}(s_j+1/e),
finite lower value h_p^mixed>=m(rho)log p, Q_p=-(b/e)log p<0. B_I-zero:
logvolume(B_I)=0. IV: H_C,inf subset pi^{j+1}B_I.

## 1. Verdict

The mixed-profile data do **not** imply B_I subset H_C,inf or h_inf>=0. The
conditional implications are valid, but the archimedean input is missing in
the frozen source.

Two conditional theorems are proved:

(A) If B_I subset H_C,inf, then h_inf>=0; if also m(rho)>=Q_p/log p, then
    h_C>=Q_p, i.e. P6 for that mixed profile.

(B) For b=273 only, a weaker arch input suffices: if h_inf>=-S3
    (S3=(12/41)log p) and m(rho)>=Q_p+S3, then h_C>=Q_p. Since m(rho)->0 as
    rho->0, such a mixed profile exists numerically. But h_inf>=-S3 is not
    proved.

Neither B_I subset H_C,inf nor h_inf>=0 nor h_inf>=-S3 follows from the mixed
finite data. The exact obstruction is the missing actual archimedean
possible-image hull/filling: IV only gives the opposite upper container.

## 2. Mixed finite value

TAME section5 mixed profile:

    m(rho)=-(1/m) sum_j rho^{j+1}(s_j+1/e),
    h_p^mixed >= m(rho) log p,
    m(rho) -> 0 as rho -> 0.                                     (2.1)

For any fixed negative Q_p, choose rho small enough that
m(rho)>=Q_p/log p (the inequality is less negative than Q). This is a
source-valid mixed profile, not an arbitrary region.

Thus the finite part can be made nonnegative (or at least above Q_p) by
mixing. But the total height is

    h_C >= m(rho)log p + h_inf.                                  (2.2)

The arch term h_inf is independent of the finite mixing parameter rho in the
frozen source.

## 3. Conditional theorem A: B_I containment

If B_I subset H_C,inf, monotonicity of normalized log-volume and
logvolume(B_I)=0 give

    h_inf >= logvolume(B_I)=0.                                   (3.1)

Then with m(rho)>=Q_p/log p,

    h_C >= m(rho)log p + h_inf >= Q_p,
    F=Q_p-h_C <= 0,                                              (3.2)

so P6 holds for that mixed profile. This is a valid conditional theorem.

## 4. Conditional theorem B: weaker arch input for b=273

For b=273, Q_p=-(273/41)log p ~ -6.659, S3=(12/41)log p ~2.756. Since
m(rho)->0, choose rho with

    m(rho) >= Q_p+S3 = -(273-12)/41 log p = -(261/41)log p ~ -3.903. (4.1)

If h_inf>=-S3, then

    h_C >= m(rho)log p + h_inf >= Q_p+S3-S3 = Q_p,                (4.2)

so P6 holds for this b=273 mixed profile. This is weaker than B_I
containment (which would give h_inf>=0), but h_inf>=-S3 is itself an open
lower bound (task-270/313); it is not a consequence of mixing.

For b=3, Q_p+S3=( -3+12)/41 log p >0, impossible for m(rho)<=0; the weaker
route does not apply.

## 5. Exact obstruction

Neither B_I subset H_C,inf nor h_inf>=0 nor h_inf>=-S3 follows from:

1. **B_I-zero normalization.** It fixes logvolume(B_I)=0 as a reference; it
   does not put B_I into the actual possible-image hull.

2. **IV container.** IV gives H_C,inf subset pi^{j+1}B_I, the opposite
   inclusion. B_I subset pi^{j+1}B_I does not imply B_I subset H_C,inf.

3. **Mixed finite good factors.** A mixed profile has good finite factors, but
   the archimedean possible-image set is a separate source object. A good
   finite label does not force a unit ball at the archimedean place; the
   Theta/Gaussian arch action depends on actual local values, not on the finite
   mixing parameter.

4. **Tensor product.** Even if one arch factor contributed a unit ball, B_I is
   a product of unit balls over all direct-summand copies; one factor's ball
   does not give the full B_I in the total arch packet.

5. **No actual H_C,inf.** Task-232 established that the actual archimedean
   possible-image set/radius is not constructed; only the IV upper container
   and B_I-zero normalization are available.

## 6. Formal countermodel to the implication

The implication "mixed profile => B_I subset H_C,inf" is not a logical
consequence of the finite mixed data. A formal arch model

    H_C,inf = r B_I,   0<r<1,                                     (6.1)

satisfies the IV container (rB_I subset pi^{j+1}B_I for r<=pi^{j+1}) and is
compatible with B_I-zero as a reference, but does not contain B_I and has
h_inf=log r<0. The mixed finite value m(rho) is unchanged. This is a
countermodel to the implication, not an actual IUT hull; it shows that an
additional arch filling/lower theorem is indispensable.

## 7. What would prove the mixed route

One would need one of:

- (A) a source theorem B_I subset H_C,inf (level-appropriate, tensor-compatible);
- (B) a source lower bound h_inf>=0 from the actual arch Theta-pilot values;
- (C) for b=273, the weaker h_inf>=-S3 plus a mixed profile with m(rho)>=Q_p+S3;
- (D) a global unit/point/region in H_C,inf whose product formula gives the
  required lower bound.

None is in the frozen source. The mixed finite profile alone cannot supply the
arch input.

## 8. Classification

| item | status |
|---|---|
| mixed finite m(rho)->0 | PROVED |
| B_I subset H_C,inf => h_inf>=0 | PROVED conditional |
| mixed + B_I containment => P6 | PROVED conditional |
| b=273 mixed + h_inf>=-S3 + m>=Q+S3 => P6 | PROVED conditional |
| mixed => B_I subset H_C,inf | FALSE as logical implication; no source proof |
| mixed => h_inf>=0 | NOT PROVED |
| mixed => h_inf>=-S3 | NOT PROVED |
| actual H_C,inf / arch filling | MISSING |
| mixed-profile P6 unconditional | NOT OBTAINED |

## 9. Conclusion

Mixing removes the finite positive-deficit obstruction but does not touch the
archimedean one. The mixed profile does not imply B_I subset H_C,inf or
h_inf>=0. The conditional implications (mixed + B_I containment => P6; b=273
mixed + h_inf>=-S3 + m(rho)>=Q+S3 => P6) are valid, but their arch hypotheses
are exactly the missing source inputs. A formal rB_I arch model shows the
implication is not automatic. Therefore the most decisive mixed-profile P6
route remains blocked at the archimedean lower bound/filling theorem, not at
the finite mixed volume.

No arbitrary r_v or region; no Lean/kernel closure; target_accepted=false;
P6 open.

## 10. Status

- Short natural-language theorem/obstruction only; no Lean/Project edits.
- Mixed finite value and conditional arch implications proved; exact missing
  arch containment/lower bound recorded.
- target_accepted=false.
