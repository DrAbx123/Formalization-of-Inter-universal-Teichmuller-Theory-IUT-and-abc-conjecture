# C9 b=273 global BPS with canonical root: construction attempt

Task ID: task-295 / C9-B273-BPS-CONSTRUCTION-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: short natural-language theorem/proof/obstruction; no arbitrary BPS data; no Lean/Project edits; only this file written.

## 0. Inputs

- C9-B273-GLOBAL-BPS-20261025.md (task-292), SHA256 1284a14a6844692f13ad8503cba10eba0526c5d0cafdae577664b251e77b6ec7.
- C9-B273-COMPLETE-BPS-20261025.md (task-288), SHA256 739757d99c6aa23cf67925e3272ea0b146066ab8a95c4486b288d1b3c906bd8b.
- C9-B273-CONSTRUCTION-20261025.md (task-257), SHA256 5353f7e8af722edf506f4c567a33ce3332d11fdcdbcbf26d69832491c148d500.
- C9-E2-COMPLETE-C-20261025.md (task-262), SHA256 e841de84fa1182074aff547ab19f0970e9292503ec2f5b45bf0d1e3583a029a8.

## 1. Local root data for E_546

Let p=12301, e=l=41, K_v=Q_p(pi), pi^41=p u. The E_546 Tate parameter is

    q=p^546 u_q,  u_q in 1+p^546 Z_p subset 1+pZ_p,                 (1.1)
    q=pi^22386 v^82,  qhat=pi^273 v,  v in 1+pZ_p,                  (1.2)
    qhat^82=q,  v_p(qhat)=273/41,  b=273.                           (1.3)

The 82nd roots of q in K_v form a torsor under mu_82. Since 82=2*41 divides p-1=12300, mu_82 is a nontrivial subgroup of Q_p^times subset K_v^times. Thus an absolute root qhat is not unique; qhat multiplied by any zeta in mu_82 is another root.

## 2. Best possible canonical normalization

Relative to a fixed uniformizer pi of K_v, there is a canonical root. Write q/pi^22386=v^82 with v in 1+pZ_p. The 82nd-power map on 1+pZ_p is bijective because p does not divide 82, so v is the unique 82nd root of q/pi^22386 in 1+pZ_p. Then

    qhat_pi := pi^273 v                                               (2.1)

is a canonical 82nd root of q **relative to pi**. Equivalently, among the 82 roots, qhat_pi is the unique one whose quotient by pi^273 lies in 1+pZ_p.

This is a genuine partial construction: it removes the mu_82 ambiguity once pi is fixed, and it constructs the local value data g_j=zeta_j qhat_pi^{j^2} (or a=qhat_pi) up to the source root unit zeta_j. It does not construct a BPS label/gluing.

## 3. No absolute canonical root

The uniformizer pi is not fixed by E_546 or by the local field alone. If pi is replaced by zeta_41 pi, then pi^273 is multiplied by zeta_41^273=zeta_41^27 (since 273=6*41+27), and qhat_pi is multiplied by zeta_41^27, another 82nd root of q. Conversely every root is obtained this way or by mu_2 (the remaining 2-torsion). Therefore:

- qhat_pi depends on the choice of pi;
- there are at least 82 distinct roots qhat corresponding to mu_82;
- no source theorem selects one root for the b=273 profile.

The unique root in 1+pZ_p after dividing by pi^273 is canonical only **relative to pi**; it is not an absolute canonical root in K_v. This is the precise obstruction to the task's 'canonical root' unless the source data include a fixed uniformizer. IUT local data do not canonically fix pi.

## 4. Global BPS remains missing

Even granting the relative canonical root qhat_pi, a global BPS/F^{⊩▶×mu}-prime-strip is not constructed. The BPS requires:

(a) the global mono-theta environment and theta/Gaussian monoids at every relevant place;
(b) the evaluation points, Kummer classes, root/cyclotome normalizations, and zero-label splitting;
(c) the labels/symmetrizing isomorphisms and gluing to the Theta-pilot 0-column;
(d) the target column and fixed q-volume class.

E_546 determines the curve and local q/root data, but not (a)-(d). The canonical local root removes one mu_82 ambiguity in the local value formula; it does not supply BPS labels, gluing, or the Theta-pilot. Task-292's non-determination theorem therefore persists: at least two BPS label/gluing structures over the same E_546 data differ in root/cyclotome/zero-label choices, and E_546 does not select one.

## 5. Short theorem

**Theorem (b=273 BPS canonical-root status).**

(a) Relative to a fixed uniformizer pi, E_546 has a canonical local 82nd root qhat_pi=pi^273 v, v the unique 82nd root of q/pi^22386 in 1+pZ_p.
(b) No absolute canonical root exists from E_546: the roots are a mu_82 torsor, mu_82 is nontrivial, and changing pi changes the root; the source does not fix pi.
(c) Even with qhat_pi, the global BPS labels/gluing/Theta-pilot 0-column are not determined; the exact obstruction is (a)-(d) of §4.
(d) Consequently the b=273 global BPS and complete C are not constructed. If a complete C with a chosen BPS/root normalization and CFTH/TC/arch were supplied, the b=273 profile would give a P6 counterexample with margin >8800; this is conditional.

**Proof.** (a) is the unique-root property on 1+pZ_p. (b) is the mu_82 torsor and pi-change computation zeta_41^273=zeta_41^27. (c) is the source role of BPS as an independent F^{⊩▶×mu}-prime-strip and Theta-pilot gluing; local q/root data do not determine it. (d) is the absence of the objects in (c), plus the conditional task-256 computation. QED.

## 6. Exact obstruction

The first missing source object remains the global BPS label/gluing and Theta-pilot 0-column, not the local b=273 q/root data. Specifically:

1. an absolute root/cyclotome normalization or a source-fixed uniformizer pi;
2. the global BPS/F^{⊩▶×mu} label set and gluing to the Theta-pilot 0-column;
3. the Theta-pilot possible-image set and target column/q-volume class;
4. explicit C_F/C_K/V/epsilon, CFTH finite branch, actual arch H_C,inf, TC-A..TC-H/TC-S.

No arbitrary root or BPS label is chosen. The relative root qhat_pi is actual but insufficient.

## 7. Status

Actual: E_546 curve, local q/qhat_pi relative canonical root, b=273, local theta/Gaussian value data.
Conditional: any complete C/BPS/Theta construction; conditional P6 counterexample.
Missing: absolute root/uniformizer normalization, global BPS labels/gluing, Theta-pilot/target, CFTH/TC/arch; complete C.
Withdrawn: absolute canonical root from E_546; global BPS construction; unconditional P6 counterexample.

target_accepted=false; complete C9/P6/ABC not proved.
