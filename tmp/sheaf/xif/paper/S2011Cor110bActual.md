# S2011: Cor 1.10(b) on the actual local data

Date: 2026-11-01.  File: tmp/sheaf/xif/paper/S2011Cor110bActual.lean.
Consumer: tmp/sheaf/xif/paper/_S2011Consumer.lean.

## Outcome

The G_v-action on the actual cohomological limit lim_J H^1(J, mu_hat^Z) is
constructed and kernel-checked (germAction : G_v ->* MulAut).  The [AbsTopIII]
Cor 1.10(b) group-theoretic algorithm and its comparison with the actual
cyclotome / Kummer image are precisely localised as missing; two pieces are
stated as named propositions and nothing is assumed in their place.

## Constructed (EXIT = 0)

conjHom, conjOpen, translateRep (conjugated domain, coefficient action on
values), translateRep_equivalent (well defined on the direct limit),
translateGerm, translateGerm_one, translateGerm_mul, translateGerm_conj,
translateGermEquiv, germAction, germAction_group_mul, germAction_act_one,
germAction_act_mul.

## Missing (in dependency order)

(M1) Verlagerung/transfer and the colimit colim_H (H^ab)_tors: Mathlib has no
     transfer for a finite-index subgroup, so mu_{Q/Z}(G_v) and mu_hat^Z(G_v)
     cannot even be formed.  First missing item.
(M2) Local reciprocity on torsion, stated as localReciprocityOnTorsion p.
(M3) Continuous H^2 and H^2(G_v, mu_hat^Z) = Z-hat: no continuous H^2 and no
     Z-hat in the tree; the source computation is lim_n Br(k_v)[n] (local CFT).
     Not statable; no declaration fabricated.
(M4) The normalized surjection: weakFrobeniusNormalization p is the strongest
     statable form (Integer instead of Z-hat, limit instead of H^1(G_v,-));
     weakFrobeniusNormalization_kernel derives the kernel statement on the
     actual Kummer image.
(M5) Joint continuity of the action: no topology on the limit in the tree.
(M6) Model caveat: the tree Kummer image is that of O^tri_{Qbar_p}, the source
     (d) is about k_v^times inside the limit.
(M7) G_v-equivariance of the actual Kummer map is not proved (route: transport
     the canonical root system and use IntegralKummerRootRealization.germ_eq).

## Evidence

* source SHA256 6452961F33F2DC21D7AD519777B80AB33F08EC760BA03D7B5858E961AAF5F159
  (471 lines), EXIT = 0, 0 errors, 0 warnings.
* olean 694,072 bytes, SHA256
  2D180185527E9E6D0A138391F36E1E7EDF714E2FD9F4676A5F1E570F59D3C399.
* axioms: propext, Classical.choice, Quot.sound only (file prints, consumer
  re-checks).
* consumer _S2011Consumer.lean: EXIT = 0, olean 3,808 bytes, SHA256
  77AC22974D889451C088C807F30734C440175082A4C995AB43B461BE3A2B32BF.

## Not run

Full Project build, target comparator, independent review, and the [AbsTopIII]
group-theoretic construction itself.

## Next executable step

(i) prove (M7); or (ii) build the Verlagerung H^ab --> G^ab for finite-index
subgroups, the prerequisite for stating (M1)-(M4) at all.


## Update 2026-11-01: M7 proved by S2016

S2016KummerEquivarianceActual.lean proves PsiCnsKummer_equivariant and germAction_mem_kummerImage. M7 is no longer missing; M1-M6 remain as stated.


## Update 2026-11-01: M1 corrected/closed by S2017

Mathlib v4.32.2 already has MonoidHom.transfer; S2017 constructs transferAb and the order-dual colimit muQZ/muHatZ. M1 is not a missing construction. First missing is now M2 (local reciprocity on torsion + transfer compatibility).
