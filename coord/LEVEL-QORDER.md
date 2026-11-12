# LEVEL-QORDER — level definitions, Ind3 increment, and the qOrder bridge

Status: READ-ONLY audit, 2026-11-12. No compile.
Question: is the source multiradial level related to qOrder by an exact formula
(level = 2l*qOrder or level = qOrder*e), and does Ind3 level increment n give a
log-volume increment linear in A?

Verdict: A = NO (no existing theorem), B = only after a new LevelQOrderBridge
with explicit definitions, C = current finite-model status (level is a free
coordinate, not qOrder).

## 1. Level: exact definitions and monotonicity lemmas

Core level, LeanFormal/IUT/IUTIII/Theorem311/MultiradialOutputKernel.lean:12-31:
  structure Core (Label Choice) where
    base : Choice
    level : Choice -> Nat
    ind1/ind2/ind3 : ...
    ind1_level : forall g c, level (ind1 g c) = level c
    ind2_level : forall g c, level (ind2 g c) = level c
    ind3_level : forall n c, level c <= level (ind3 n c)
The level is an arbitrary function Choice -> Nat; Core only records invariance
under Ind1/Ind2 and monotonicity under Ind3.

Carrier strengthening, ParametricCarrier.lean:25-33:
  ind3_level_eq : forall n c,
    core.level (core.ind3 n c) = core.level c + n.
This is a field of Carrier, not derived from qOrder.

Source finite model, SourceFiniteMultiradial.lean:20-69:
  core l := { level := fun c => c.upperSemiLevel, ind3 := ProcessionChoice.ind3Lift, ... }
  core_ind3_level : ... = c.upperSemiLevel + n   [rfl]
ProcessionChoice, ConcreteFiniteModel.lean:98-164:
  structure ProcessionChoice where
    processionLabel : finiteLabel l
    tensorLabel : finiteLabel l
    upperSemiLevel : Nat
  base.upperSemiLevel = 0
  ind1Act does not change upperSemiLevel
  ind2Act does not change upperSemiLevel
  ind3Lift n c := { c with upperSemiLevel := c.upperSemiLevel + n }
  ind3_upperSemiLevel : (ind3Lift n c).upperSemiLevel = c.upperSemiLevel + n  [rfl]

Log-volume in the finite model, ConcreteFiniteModel.lean:329-359:
  normalizedLogVolume l c = thetaLogVolume l + (c.upperSemiLevel : Real).
  normalizedLogVolume_ind3Lift_add (SourceK1K2CardReduction.lean:194-199):
    normalizedLogVolume l (ind3Lift n c) =
      normalizedLogVolume l c + (n : Real).
So in this finite model the Ind3 log-volume increment is exactly n, but n is an
abstract level coordinate, not qOrder.

There is no identifier sourceMultiradialLevel in the audited tree; the
source-level multiradial level currently in use is SourceFiniteMultiradial.core.level
= ProcessionChoice.upperSemiLevel.

## 2. qOrder: exact definitions and the qroot order theorem

InitialThetaData.qOrder, Iut/Cor312/ThetaData/Basic.lean:171-182:
  noncomputable def qOrder (w : FinitePlace D.F)
      (hw : w in badPlacesOver D.F D.E D.VBad) : Nat :=
    qOrderAt D.E (D.mult_of_mem_bad hw)
  qOrder_eq_orderNat : qOrder = orderNat of the Tate parameter
  qOrder_pos : 0 < qOrder
  coprime_qOrder : Nat.Coprime D.l (qOrder w hw)

qroot, Iut/Concrete/ThetaLocalConstruct/Data.lean:281-330:
  qrootOf D v = chosen 2l-th root of the Tate parameter at bad v, 1 elsewhere;
  qrootOf_spec : qrootOf D v ^ (2*l) = (tate parameter q_v);
  ordp_qrootOf (v lies over w, w bad):
    ordp D.Kt v (qrootOf D v) =
      (D.qOrder w hw : Real) / (2 * D.l * ramIdx D.F w).

Thus the only proved relation between qOrder and the root/log side is
  ord(qroot) = qOrder / (2*l*e_w),
i.e. qroot^{2l} has order qOrder, and one qroot factor contributes
qOrder/(2l e) in the valuation.

## 3. Is level related to qOrder in the tree?

No. The finite model's level is a free Nat coordinate (upperSemiLevel) of
ProcessionChoice; ProcessionChoice has no qOrder field and no theorem equating
upperSemiLevel with qOrder, 2l*qOrder, or qOrder*e. Conversely, qOrder is defined
on InitialThetaData, and there is no map from ProcessionChoice to
InitialThetaData or to its qOrder.

The two objects live in different layers:
- level: Theorem311 finite multiradial carrier, an abstract monotone Nat;
- qOrder: InitialThetaData/Tate parameter arithmetic, a positive integer with
  qroot order qOrder/(2l e).

No theorem in either direction exists. Therefore:
  level = 2l*qOrder   [not proved]
  level = qOrder*e    [not proved]
  level = qOrder      [not proved]
are all GAPs, not rfl.

## 4. Bridge candidate (conditional B)

Define an explicit bridge record (target data, no inhabitant):

  structure LevelQOrderBridge
      (l : PrimeGeFive) (D : InitialThetaData l)
      (C : Carrier (finiteLabel l) (ProcessionChoice l)) where
    levelOfQOrder : ProcessionChoice l -> Nat
    level_eq : forall c, C.core.level c = levelOfQOrder c
    qOrderOfChoice : ProcessionChoice l -> Nat
    qOrder_eq : forall c, levelOfQOrder c = k * qOrderOfChoice c
    ind3_qOrder : forall n c,
      qOrderOfChoice (ProcessionChoice.ind3Lift n c) =
        qOrderOfChoice c + n
    logVolume_scaling : forall n c,
      E (ProcessionChoice.ind3Lift n c) =
        E c + n * boundaryIncrement
    boundaryIncrement : Real
    boundary_eq_A : boundaryIncrement = (j^2 / e) * A

None of these fields is currently constructed; level_eq/qOrder_eq are the exact
missing identifications. k is a normalization constant (candidate 1, 2l, or e),
not fixed by the tree.

If such a bridge is supplied, the growth formula is:

  E(n) = E(0) + n * boundaryIncrement,
  boundaryIncrement = j^2 * ord(qroot) * log p
                    = j^2 * (qOrder/(2l e)) * log p
                    = (j^2 / e) * A,
where A = qOrder*log p/(2l) (q-pilot absolute log), j is the fixed theta label
of the Ind3 scaling, and e is the local ramification index.

This is a candidate conditional formula, not a theorem. It is linear in A only
under the extra assumptions (fixed j, fixed e, per-level qroot factor, and
level/qOrder proportionality).

## 5. What the tree actually proves about growth

- Finite model: normalizedLogVolume(l, ind3Lift n c) = normalizedLogVolume(l,c)
  + n. This is exact but n is an abstract level, not A.
- qroot: ordp(qroot) = qOrder/(2l e). This is exact but scalar/local; it does
  not mention level or normalizedLogVolume.
- No theorem composes the two. The composition is exactly the missing
  LevelQOrderBridge.

## 6. A/B/C judgment

A (direct instance): NO. There is no existing level = qOrder formula and no
theorem deriving the E growth from qOrder; the finite-model increment is n, not
A.

B (conditional): YES, but only after constructing LevelQOrderBridge with:
  - a level function defined from qOrder (choice of k),
  - an Ind3 correspondence qOrder(choice after n) = qOrder(choice)+n,
  - the per-level boundary increment j^2*ord(qroot)*log p,
  - a fixed label/ramification normalization.
Then E(n) = E(0) + n*(j^2/e)*A is a conditional linear growth formula.

C (current status): the finite model's ΔE = n is an abstract model statement;
qOrder/qroot is a separate arithmetic layer. Identifying them is GAP, and
claiming E ≈ boundary*n without the bridge would be only a restatement/model
assumption.

## 7. Minimal new declarations

1. LevelQOrderBridge (explicit data; no fake inhabitant).
2. qOrderOfChoice / levelOfQOrder definitions and their equality to core.level.
3. ind3_qOrder increment law.
4. logVolume_scaling law and boundaryIncrement definition.
5. boundary_eq_A from ordp_qrootOf plus A = qOrder logp/(2l).
6. A proof that the finite model's upperSemiLevel can be instantiated by this
   qOrder-derived level without changing the existing Carrier fields.

No Lean file written; no compile claimed.
