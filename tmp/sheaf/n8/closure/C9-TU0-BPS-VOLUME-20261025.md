# C9 T_U0: BPS/root/cyclotome label volume invariance

Task: task-306. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits, no arbitrary data.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- C9-MASTER-V3-20261025.md, 335 lines,
  SHA256 3e6e9595ed8d865000e42531806149deeb33d420c277fef9a59c12fe8d455bd4.
- C9-THETA-ROOT-CANONICAL-20261025.md (task-294), 104 lines,
  SHA256 42c1cab049ba74d6e5ed2be8399c1eb74321556db592eff7975d24cc2729ab78.
- C9-BPS-AMBIGUITY-AUDIT-20261025.md (task-292/296), 183 lines,
  SHA256 8af187b674097abbabc3ff58634d8fa90eae3baa8042edc7b11276a5fdfc8739.
- C9-B273-BPS-CONSTRUCTION-20261025.md (relative root), 85 lines,
  SHA256 d572d9c31b5d195848ee33db39d2563c26e4e6855f211fae30ba1cd73f451e24.
- C9-S2-UPPER-INDEPENDENT-20261025.md (task-302), 136 lines,
  SHA256 33fc2c9fdb703d2eba3da2dd3176d5772190e11466d4a6464c95897793ea2ef7.

T_U0 as stated in Master v3: admissible theta root/cyclotome choices act by
roots of unity (or zero normalized log-volume), so the normalized log-volume
of the target hull is independent of the BPS root/label choice.

## 1. Verdict

**T_U0 is TRUE for the admissible root/cyclotome choices, but only at the
root/cyclotome level.** The proof:

- an admissible theta root choice changes qhat by a root of unity
  zeta in mu_82; different uniformizer choices change it by mu_41;
- multiplication by a root of unity is a normalized-volume isometry at both
  finite and archimedean places (finite: zeta in O_K^times, p-adic log zeta=0;
  arch: |zeta|=1 and rotation is measure-preserving);
- the physical theta/Gaussian profile g_j=zeta_j a^{j^2} is invariant under
  the combined root rotation a->zeta a, zeta_j->zeta^{-j^2} zeta_j; the
  products g_j, Kummer classes, Theta values and q-target column are unchanged,
  not merely equal in volume.

Therefore the normalized hull height h_C does not depend on the root/cyclotome
choice. If a volume-level target-upper statement (SAT-U) is proved for one
root representative, it holds for every admissible root representative.

However:

- T_U0 does **not** prove SAT-U. It removes the root-label ambiguity only; the
  target-upper inclusion H_C subset R_B+arch remains missing.
- T_U0 does **not** cover arbitrary BPS/Theta/gluing/zero-column label changes
  that alter the q/BPS row, branch, weights, or target column. Those are not
  root-of-unity choices; changing them can change normalized volume. Such a
  change is a different profile/target, not an admissible root choice.

## 2. Root choices are roots of unity

For E_546, q=p^546 u, qhat=q^{1/82}=pi^273 v. The 82nd roots of q are a
mu_82-torsor. A change of uniformizer pi->zeta_41 pi changes

    pi^273 -> zeta_41^273 pi^273 = zeta_41^27 pi^273,  273=6*41+27,  (2.1)

another 82nd root. Combining mu_41 and mu_2 gives all 82 roots. Thus any
admissible root/cyclotome choice differs by multiplication by a root of unity

    qhat' = zeta qhat,  zeta in mu_82 subset O_K^times.               (2.2)

This is the same mu-torsor described in task-294/task-296; the root choice is
not a continuous parameter.

## 3. Root-of-unity isometry of normalized volume

Let K_v be the local field, O_v its ring of integers, m_v its maximal ideal,
and B_I the B_I-zero reference unit ball (log-volume 0). For zeta a root of
unity in K_v^times:

- zeta in O_v^times; multiplication by zeta preserves O_v, m_v, J_v and every
  principal unit filtration U^n. It is a measure-preserving automorphism of
  the additive normalized-volume space.
- p-adic log(zeta)=0 (Teichmuller root of unity), so log-volumes of local
  units/q-pilot values are unchanged.
- At an archimedean place, |zeta|_v=1 and multiplication by zeta is a rotation;
  it preserves the radial coordinate and is measure-preserving on the angular
  torus. The normalized log-volume, including the angular term, is unchanged.

Hence for any measurable normalized-volume region R,

    vol_norm(zeta R)=vol_norm(R),  h_inf(zeta R)=h_inf(R).            (3.1)

This is an exact local computation, not an arbitrary normalization.

## 4. Absorption and physical invariance

Task-294's absorption theorem: let a'=zeta a and zeta'_j=zeta^{-j^2} zeta_j.
Then

    g'_j=zeta'_j (a')^{j^2}=zeta_j a^{j^2}=g_j.                     (4.1)

Thus the physical theta/Gaussian profile, its products, Kummer classes, Theta
values, and q/BPS target column are **exactly invariant**, not just
volume-invariant. In particular:

- no absolute canonical 82nd root is needed to define the physical profile;
- the root rotation is an auxiliary coordinate, not two admissible BPS value
  structures;
- the normalized hull volume is independent of that coordinate.

This proves T_U0 for root/cyclotome choices.

## 5. What T_U0 reduces

If SAT-U is the volume-level statement

    h_C <= H_B + h_inf,                                             (5.1)

then T_U0 says (5.1) is independent of the root/cyclotome representative: one
may compute h_C with any admissible root choice and the same value results.
Thus the missing absolute root/cyclotome label no longer blocks a volume-level
proof of U.

But T_U0 does **not** reduce SAT-U to a proved statement:

- the target-upper inclusion H_C subset R_B+arch (S2) is still missing;
- other local types, good places, aggregate B=I, additional q/BPS rows and
  target-column choices are not root rotations; their volume effect is not
  covered;
- global BPS/Theta gluing and zero-column labels are not canonically fixed;
  if such a label changes the q/BPS row/branch/weights, the normalized volume
  can change. This is a different target/profile, not an admissible root-label
  ambiguity.

T_U0 therefore removes one obstruction (root-label ambiguity) but leaves the
volume-level target saturation as the exact remaining gap.

## 6. What would be a counterexample to T_U0?

A genuine counterexample would need two **admissible root/cyclotome choices**
of the same BPS datum with different normalized hull volume. We proved this
cannot happen: every admissible root choice differs by a root of unity, and
root-of-unity multiplication preserves normalized volume; absorption makes the
physical g_j profile exactly invariant.

A change of BPS branch/row/weights can change the volume, but it is not a root
choice; it changes the profile/target. For example, the B=O_K row height H_A
and B=I row height H_B differ by Delta_B>0; choosing the branch is not a
root-label choice and cannot be used to disprove T_U0. It is exactly the
missing actual BPS branch/saturation data.

Thus T_U0 has no counterexample in the admissible root/cyclotome class; its
truth is limited to that class.

## 7. Classification

| item | status |
|---|---|
| admissible root choice differs by zeta in mu_82 | PROVED |
| root-of-unity multiplication preserves normalized volume | PROVED |
| absorption g_j invariant | PROVED (task-294/296) |
| T_U0 for root/cyclotome choices | PROVED |
| T_U0 for arbitrary BPS/gluing/row/weight labels | FALSE/NOT CLAIMED; can change volume/profile |
| T_U0 implies SAT-U | FALSE; only removes root-label ambiguity |
| SAT-U volume-level target saturation | STILL MISSING |
| b=273 counterexample via T_U0 | NOT OBTAINED |

## 8. Conclusion

T_U0 is true for the admissible theta root/cyclotome choices: they are
roots of unity, multiplication by a root of unity is a normalized-volume
isometry, and the physical BPS profile is exactly invariant under the absorbed
root rotation. Therefore the normalized hull volume does not depend on the
absolute root/cyclotome label, and SAT-U can be formulated at volume level
without choosing that label.

This is a genuine reduction of the root-label obstruction, not a proof of U.
T_U0 does not cover arbitrary BPS/gluing/row/weight changes; those can change
the volume and are different profile/target data. The volume-level target
saturation H_C subset R_B+arch (S2) remains the exact missing theorem. No
b=273 counterexample follows from T_U0 alone.

No arbitrary data; no Lean/kernel closure; target_accepted=false; P6 open.

## 9. Status

- Short natural-language theorem/proof only; no Lean/Project edits.
- T_U0 proved for root/cyclotome choices; reduction of SAT-U to volume level
  recorded; exact remaining S2/saturation obstruction.
- target_accepted=false.
