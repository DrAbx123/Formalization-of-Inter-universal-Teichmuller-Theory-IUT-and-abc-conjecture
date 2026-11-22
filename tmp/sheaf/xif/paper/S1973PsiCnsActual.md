# S1973: actual local constant monoid, G_v-action, diagonal units, and the first missing Psi_cns

Date: 2026-11-01.  File: tmp/sheaf/xif/paper/S1973PsiCnsActual.lean.

## Outcome

**Actual model constructed; paper-level Psi_cns remains the exact first missing.**

The file constructs, kernel-checked, the actual local G_v-monoid model
`PsiCnsModel v = IndIntegralMonoid (QPlace v)` with the actual Krull action
`psiCnsAction v : G_v ->* MulAut (PsiCnsModel v)`, its unit action, and the
G_v-equivariant monoid isomorphism to the source MLF integral monoid.  It also
constructs the actual diagonal cyclotomic subgroup of order `l - 1` inside the
product of the unit copies, proves its G_v-stability, and forms the Psi_env /
Psi_gau evaluation and the domain/codomain splittings on the actual model.

It does **not** construct the paper's cohomological constant monoid
`Psi_cns(Pi_v) subset lim H^1(J, mu_hat^Z(G_v))` or identify it with the
actual model.  No fake monoid, empty type, arbitrary inhabitant, axiom or
sorry is used.

## Constructed (EXIT=0)

1. `PsiCnsModel v`, `psiCnsAction v`, `psiCns_smul_mul`.
2. `PsiCnsUnits v`, `psiCnsUnitsAction v`, `psiCnsUnits_smul_val`.
3. `GMonoidEquiv`, `psiCnsEquivSourceMLF v`: the IndIntegralMonoid model is
   isomorphic as a G_v-monoid to the actual source MLF integral monoid.  This
   is an identification of two actual local-field models, not of the paper's
   cohomological Psi_cns.
4. `psiCnsIndTopology v` and `psiCns_continuous_action v sigma`: the actual
   ind-topology and pointwise continuity of every Krull automorphism.
5. `rootsOfUnity (l - 1) (LocalClosure v)` units of the actual integral
   monoid: `rootOfUnityInd`, `rootOfUnityUnit`, `rootOfUnityUnitHom`,
   `galoisOnRootsOfUnityAction`, `rootOfUnityUnit_galois_smul`.
6. `diagonalFlStarUnits v l`: the diagonal cyclotomic subgroup inside the
   product over theta labels, with `diagonalFlStarUnits_card` proving its
   cardinality is `l - 1 = |F_l^star|`, and
   `diagonalFlStarUnits_galois_smul_mem` proving G_v-stability.
7. `PsiEnvModel v`, `PsiGauModel v l`, `psiEvaluation v l`,
   `psiEvaluation_bijective`, `psiEvaluation_units`,
   `psiEvaluation_generator`, the unit/ray splittings
   `psiEnvUnitSection`, `psiEnvRaySection`, `psiGauUnitSection`,
   `psiGauRaySection`, and the evaluation compatibility laws
   `psiEvaluation_unitSection`, `psiEvaluation_raySection`.
8. `diagonalFlStarUnitsInGau_val_mem_localGaussian`: the diagonal units are
   units of the ambient product and land in S1966's local Gaussian monoid.

## Exact first missing

The first missing object is the [AbsTopIII], Corollary 1.10, (b), functorial
group-theoretic algorithm producing the ind-topological submonoid

  Psi_cns(G_v) subset lim_J H^1(J, mu_hat^Z(G_v)),

naturally isomorphic to O^tri_{F_v}, with its natural G_v-action.  This needs
(a) the continuous-cohomology limit over the open subgroups of the local
absolute Galois group, (b) the actual coefficient cyclotome
`mu_hat^Z(G_v)`, (c) the [AbsTopIII] algorithm selecting the submonoid and
identifying it with O^tri, and (d) compatibility with the Krull action on the
actual local field.  None of these is in the tree.

The second missing point is `PsiCnsJointContinuousActionMissing v`: joint
continuity of the action map `G_v x PsiCnsModel v -> PsiCnsModel v` for the
ind-topology.  Pointwise continuity is proved; S1962 records the same
continuity-with-parameters gap.

The third missing point is the paper's F_l^star-symmetrizing isomorphisms
between the labeled copies.  The cyclotomic subgroup and its diagonal
embedding are actual, but the label symmetries themselves are not constructed.

## Evidence

* source SHA256:
  26E1117EE0EFA271E3911FFE9CF8E6546BAAC0C4179EAEC33630B360C544303D
* EXIT=0:
  `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1973PsiCnsActual.olean tmp/sheaf/xif/paper/S1973PsiCnsActual.lean`
* olean: 1,042,632 bytes, SHA256
  5CF78C843CD75DC922CD4EDD9395682ED00517EA93E2E7E8008B778BCA39286E
* axioms: propext, Classical.choice, Quot.sound only; no sorryAx, no custom
  axiom (checked by the file's #print axioms and the consumer).
* consumer: tmp/sheaf/xif/paper/_S1973Consumer.lean, EXIT=0, olean 2,728
  bytes, SHA256
  B42DB055AEDFE838F0BE66FB4062C048C3C3C6D95D0B05727309AE9C097CB39C.

## Not run

Full Project build, target comparator, independent review, and the paper-level
cohomological construction itself.

## Next executable step

Construct the [AbsTopIII] cohomological Psi_cns algorithm or prove that the
actual IndIntegralMonoid model is isomorphic to its output as a G_v-monoid.
Only after that can the present diagonal/evaluation/splitting model be promoted
from a model to the paper's Psi_env / Psi_gau.
