# 原文对象对齐（paper text first）

本文件只按原文定义对齐；Lean 名字仅作“当前表示”参考。

## 0. 目标原文

IUT III, Corollary 3.12 (lines 10324-10353):

  -|log(Theta)| := procession-normalized mono-analytic log-volume
    of the holomorphic hull of the union of possible images of a
    Theta-pilot object, relative to the relevant Kummer isomorphisms,
    in the multiradial representation, subject to (Ind1),(Ind2),(Ind3).

  -|log(q)| := procession-normalized mono-analytic log-volume
    of the image of a q-pilot object, relative to the same Kummer
    isomorphisms, in the multiradial representation, NOT subject to
    (Ind1),(Ind2),(Ind3).

  Then -|log(Theta)| >= -|log(q)|.

## 1. 原文对象清单

### P1. Initial Theta-data
IUT I Def 3.1: (F/F, X_F, l, C_K, V, V_bad, V_bad^mod, epsilon).
Source: `InitialThetaArithmeticData`, `SourceNativeInitialThetaData`.
Status: source-level actual.

### P2. Theta±ellNF-Hodge theaters / D-Theta±ellNF-Hodge theater
IUT III Thm 3.11 opening (lines 9151-9163); log-theta-lattice.
Source: Hodge theater / prime-strip structures; actual in source layer.

### P3. Procession of D^⊢-prime-strips
IUT III Thm 3.11 (i) (lines 9164-9175):
  Prc(n,°D^⊢_T) = {n,°D^⊢_0} -> ... -> {n,°D^⊢_0,...,n,°D^⊢_{l*}}.
Status: procession data exists; must be used as Ind1 carrier.

### P4. Local mono-analytic tensor packets and IQ
IUT III Thm 3.11 (i)(a) (lines 9176-9191):
  I(S±_{j+1}; n,°D^⊢_{vQ}) ⊆ IQ(S±_{j+1}; n,°D^⊢_{vQ}),
  I(S±_{j+1,j}; n,°D^⊢_v) ⊆ IQ(S±_{j+1,j}; n,°D^⊢_v),
  equipped with procession-normalized mono-analytic log-volumes (Prop 3.9(ii)).
Status: C3 multi-factor tensor block and local Haar/log-volume exist;
the literal IQ carrier and full procession-normalized log-volume still need
alignment (see G1/G6).

### P5. Multi-factor index set A
IUT III Prop 3.1/3.2: {αF}_{α∈A} is an n-capsule;
  log(A F_{vQ}) = tensor_{α∈A} log(F_{vα}).
A is generally NOT a singleton (source docs iut-iii/iut-iv).
Status: C3 multi-factor carrier exists; qVFam Unit is only one-factor
specialization and is NOT the paper A-carrier (G2).

### P6. Splitting monoid and its action
IUT III Thm 3.11 (i)(b) (lines 9192-9221):
  Psi^⊥_{LGP}(n,°HT)_{v}, v∈V_bad,
  as a subset of prod_{j∈F_l^×} IQ(S±_{j+1,j}; n,°D^⊢_v),
  with multiplicative action.
Status: source-level splitting monoid/action; needs alignment.

### P7. Global number fields / Frobenioids / degrees
IUT III Thm 3.11 (i)(c) (lines 9222-9253):
  M^⊛_{MOD}(...)_j = M^⊛_{mod}(...)_j ⊆ IQ(S±_{j+1}; n,°D^⊢_{V_Q})
    = prod_{vQ∈V_Q} IQ(...),
  natural isomorphisms of global Frobenioids, global degrees via log-volumes.
Status: source Frobenioid layer; not yet tied to C3 tensor log-volume.

### P8. Theta-pilot object
IUT III Def 3.8 (i) (lines 6617-6655):
  object of prod_{j∈F_l^×} (F^⊛_MOD)_j or (F^⊛_mod)_j
  determined by a collection, indexed by v∈V_bad, of generators up to torsion
  of the monoids Psi^⊥_{F_lgp}(...)v.
Status: source-level ThetaPilotObject; actual Frobenioid object not constructed.

### P9. q-pilot object
IUT III Def 3.8 (i) (lines 6643-6655):
  object of the global realified Frobenioid C^⊩_△ determined by a collection,
  indexed by v∈V_bad, of generators up to torsion of the splitting monoid
  of the split Frobenioid F^⊢_{△,v}; concretely determined by the q_v.
Status: q_v family actual; full q-pilot Frobenioid object not constructed.

### P10. Theta×mu_LGP-link / Theta×mu_lgp-link
IUT III Def 3.8 (ii)-(iii): full poly-isomorphisms of F^⊩▶×mu-prime-strips
relative to a log-link.
Status: source-level link actions; actual object construction incomplete.

### P11. Kummer isomorphisms / log-Kummer correspondence
IUT III Thm 3.11 (ii) (from line 9296):
  isomorphisms between vertically coric data (a),(b),(c) and data from each
  Hodge theater, including local/global tensor packets and Frobenioids.
Status: source-level Kummer actions exist; literal IQ isomorphisms missing.

### P12. Indeterminacies
IUT III Thm 3.11 (i) (lines 9258-9275):
  (Ind1) automorphisms of the procession Prc(n,°D^⊢_T);
  (Ind2) for vQ∈V_Q^non (resp. V_Q^arc), independent copies of Ism
         (resp. order-2 automorphisms) acting on each direct summand of the
         j+1 factors in the tensor product defining IQ;
  (Ind3) final portion of Thm 3.11 (ii): indeterminacy of the log-Kummer
         correspondence / evaluation (lines 9589-9615).
Status: Ind1 multi-factor reindex exists (`PrcAutomorphismTensorAction`);
Ind2/Ind3 actual actions on the multi-factor C3 packet and their union are gaps.

### P13. Holomorphic hull
IUT III Remark 3.9.5 (i) (lines 7658-7680):
  for alphaU ⊆ IQ(alphaF_{vQ}) relatively compact with finite log-volume,
  the holomorphic hull is the smallest subset of the form
    alphaH = lambda · O_{alphaF_{vQ}},
  where every component of lambda is nonzero, containing alphaU;
  if alphaU is not relatively compact, hull = whole IQ.
  (ii) phi(P) = intersection_{H ⊇ P} H, with (P1),(P2),(P3).
Status: value-level `sourceHolomorphicHull` exists; literal lambda·O hull
on the C3/IQ carrier is missing (G6).

### P14. Procession-normalized mono-analytic log-volume
IUT III Prop 3.9 (i),(ii) and Remark 3.1.1 (ii)-(iv):
  mu_log = procession-normalized mono-analytic log-volume,
  average over j∈F_l^×.
Status: local C3 Haar/log-volume and a product/procession factor exist;
the full multiradial procession-normalized mu_log is not aligned (G6).

### P15. Theta values and mu_{2l}
IUT III Fig. 3.4 (lines 10310-10315) and IUT I/II:
  theta values {q_v^(j^2)}_{j=1,...,l*}, subject to mu_{2l}.
  q_v^(1/2l) is a 2l-th root of q_v in K_v (IUT I line 3707),
  using 2-torsion (IUT I Def 3.1(b)).
Status: algebraic-closure root/ThetaLabel actual but auxiliary;
completion root in K_v is missing (G3); q_v 2l-th power not derived from
Torsion23Rational; Q_5 counterexample for arbitrary q.

### P16. q-pilot log
IUT III lines 7475-7480:
  log(q) = ord_v(q_v) * log(p_v).
Status: classical q-pilot log actual = sum weight*order*log p;
identification with q-pilot image log-volume is missing (G8).

## 2. 缺口（按 paper object 编号）

G1. P4/P5: literal IQ carrier + A/index to C3 tensor index and place agreement.
    Existing exact gap: `PrimeStripC3PlaceComparisonRequired`.
G2. P5: qVFamTensorV = Unit is a one-factor specialization, not paper A.
    Must replace by the multi-factor C3 carrier for the paper tensor.
G3. P15: q_v^(1/2l) in K_v. Source only has Torsion23Rational (6-torsion
    rational), no bridge to NatRootSystem (qVUnit); Q_5 counterexample shows
    arbitrary q has no root. This is the real arithmetic blocker.
G4. P8: actual Theta-pilot Frobenioid object and its possible images.
G5. P9: actual q-pilot Frobenioid object; qVFamily collection is only input.
G6. P13/P14: literal lambda·O hull and procession-normalized mu_log on the
    multi-factor C3/IQ carrier, including the average over j∈F_l^×.
G7. P12: Ind2/Ind3 actions on the multi-factor C3 j+1 tensor; Ind1 actual
    reindex exists; union of possible images under all three is missing.
G8. P16: identify q-pilot image log-volume with classical q-pilot log.
G9. P11: literal Kummer isomorphisms on the IQ carrier, not just source-level
    tensor actions.
G10. Final Cor3.12 comparison: construct StepXIContract/IQHullLogVolume
     from source; repo only has conditional contract assembly.

## 3. 构造顺序（原文对象优先）

1. G1+G2: use the existing multi-factor C3 carrier; construct actual
   A/V ↔ C3.tensorIndex comparison and Ind1 compatibility. Do not use qVFam Unit.
2. G3: construct completion q_v^(1/2l) from 2-torsion or record exact
   missing source theorem. Without this, Theta values cannot be actual.
3. G7: construct Ind2/Ind3 on the multi-factor packet and the possible-image union.
4. G6: construct literal lambda·O hull and procession-normalized mu_log on C3/IQ.
5. G4+G5: actual Theta/q-pilot Frobenioid objects and their images.
6. G8+G9: identify q-pilot log-volume and Kummer isomorphisms.
7. G10: assemble the final comparison.

## 4. 结论

Paper target is NOT currently formalized end-to-end.  The main gaps are not
normalization tricks: they are the literal IQ/C3 multi-factor carrier, the
A/index comparison, the completion 2l-th root, the literal lambda·O hull and
procession-normalized mu_log, and the actual pilot-object/Frobenioid layers.
