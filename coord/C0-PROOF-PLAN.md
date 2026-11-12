# C0-PROOF-PLAN — self-contained formalization plan for the six missing lemmas

Status: READ-ONLY PLAN, 2026-11-12. No Lean file written, no compile run.
Source of the six gaps: coord/C0-EXACT-DERIVATION.md. Root sources: Iut/ lana tree.
Oleans: only Iut/Concrete/LocalConstruct/Haar.olean is present; all C0 modules below
(Basic/Forms, Gap, VcI, Volume, ScaleVolume, ArchLogShell, Archimedean, IndAut, Theory,
LogShell, ThetaRegion, Cor312/Statement, Wall/IdentifiedCopies) have NO oleans. Therefore
none of the lemmas can be compiled by our lane until the lana root is built by the
watchdog/mainline. No TG dependency is visible in the import chain; the blocker is
missing lana oleans, not an absent paper input.

Important correction before the six items: the radius in C0 A3' is not established as
pi^m. The source has only archLogShell_subset with (sqrt 2 * pi)^m, while VcI.md gives the
exact hull scalar sqrt(N) * pi^m, N = 2^(m-1). These differ by sqrt(2)^m. The plan below
uses an explicit archHullScale and does not assert pi^m.

## 1. Dependency graph

Existing green definitions (source-level; no oleans):
- LocalTheory.leastHull (Iut/WallEquiv/Gap.lean:87); leastHull_eq (:97),
  leastHull_subset (:93), exists_leastHull_eq (:107), leastHull_smul_integral (:138),
  leastHull_units_smul (:148), componentVol_le_leastHull (:130),
  componentVol_le_leastHull_self (:143).
- LocalTheory.componentVol (Iut/Concrete/LocalConstruct/Volume.lean:196);
  componentVol_integral (:201), componentVol_mono (:206),
  componentVol_arch_scale (:251), finrank_tensor_eq_card (:219).
- LocalConstruct.haar_units_smul (ScaleVolume.lean:46); unitModulus (:40);
  componentVol_units_smul_integral (:52); componentVol_prod_incl_smul_integral (:118).
- LocalConstruct.componentVol_units_smul (Iut/Wall/IdentifiedCopies.lean:67) ALREADY
  EXISTS: mu^log(a*X) = mu^log(a*O) + mu^log(X) for 0 < mu X < infinity.
  This means C0 item 3 is not a gap; it is a green source theorem, but its olean is absent.
- LocalTheory.shell (Theory.lean:120), integral (:103), tuple/incl; InitialThetaData:
  scaleElt (ThetaRegion.lean:136), scaleEltAt (:126), thetaFiniteOn (:170),
  thetaFinite_eq (:261), thetaComponent (:257), tensorAut (IndAut.lean:219),
  tensorAut_thetaShell_admissible (:283).
- LocalConstruct.archLogShell (ArchLogShell.lean:278); archLogShell_eq_preimage (:285);
  archTensorBasis (:227), archTensorInner_basis (:231), archTensorCoord (:250),
  norm_archTensorCoord_sq (:256), card_archTensorIdx (:335), archLogShell_subset (:374).
- LocalConstruct.archIntegral (Archimedean.lean:328); archIntegral_eq_preimage (:334);
  exists_forall_archChar_eq (:284); mem_algebraMap_smul_archIntegral (:394);
  isUnit_iff_forall_archChar_ne_zero (:302).
- LocalTheory.archDefect (Gap.lean:459); archDefect_nonneg (:463), archDefect_pos (:468);
  componentVol_archLogShell_lt_leastHull (:362).
- InitialThetaData.ind2Term (Gap.lean:747); ind2Term_nonneg (:756);
  ind2Term_eq_zero (:771); thetaComponent_finite_of_not_bad (:725);
  scaleElt_eq_one (ThetaRegion.lean:?); ordp_qroot (ThetaLocalConstruct/Data.lean:420).

New dependency order:
A. componentVol_units_smul (exists) -> used by ind2Term final.
B. archTensorCoord measure comparison (new) -> ball/polydisc volumes (new) ->
   leastHull_archLogShell scalar (new) -> archDefect_eq (new).
C. thetaComponent exact p-order (new orbit lemma) -> leastHull_thetaComponent_eq_pow_floor
   (new) -> ind2Term exact value (new).
D. Both A/C need componentVol_units_smul and componentVol_arch_scale.

              +-- componentVol_units_smul (green)
              +-- tensorAut/thetaFinite_eq
C -> thetaComponent p-order -> leastHull_thetaComponent_eq_pow_floor -> ind2Term exact
              +-- ordp_qroot / scaleElt

              +-- archTensorCoord + Haar uniqueness
              +-- volume_ball / volume_polydisc
B -> arch measure comparison -> arch hull scalar -> archDefect_eq
              +-- leastHull/exists_leastHull_eq
              +-- archIntegral/archIntegral_eq_preimage

## 2. The six lemmas: statements and proof plans

Notation for every item: K is a number field, iota finite, c : iota -> Place K,
p : Nat.Primes, Tensor K vQ c is the packet, integralAt/haar/componentVol are the
LocalConstruct definitions above.

### Lemma 1. componentVol_units_smul (already green, no new proof needed)

Exact existing statement (Iut/Wall/IdentifiedCopies.lean:67):
  theorem componentVol_units_smul {a : Tensor K (.finite p) c} (ha : IsUnit a)
      {X : Set (Tensor K (.finite p) c)} (hX : 0 < haar (.finite p) c X)
      (hX' : haar (.finite p) c X < top) :
      componentVol (.finite p) c (a • X) =
        componentVol (.finite p) c (a • integralAt (.finite p) c) +
          componentVol (.finite p) c X

The C0 intended corollary is:
  lemma componentVol_units_smul_log (a : (Tensor K (.finite p) c)^x)
      {X} (hX : 0 < haar X) (hX' : haar X < top) :
      componentVol (.finite p) c ((a : _) • X) =
        Real.log (unitModulus p c a) /
          Module.finrank Q_p (Tensor K (.finite p) c) + componentVol X
  Proof: existing componentVol_units_smul + componentVol_units_smul_integral (:52).
  Status: GREEN source, no olean; directly writable once ScaleVolume/IdentifiedCopies
  oleans exist. No new Mathlib fact.

### Lemma 2. leastHull_thetaComponent_eq_pow_floor (core Ind2 gap)

Needed new definition (suggested in a new file after Gap/ThetaRegion compile):
  noncomputable def ind2Exponent (D : InitialThetaData) (i : Fin (nC D))
      (p : Nat.Primes)
      (c : Lab (nC D) i -> LocalTheory.Fiber D.Fmod (.finite p)) : Real :=
    ((i.1 + 1 : Real) ^ 2) *
      ordp D.Kt
        (LocalTheory.sectPlace D.placeSect (c (distinguished (nC D) i)))
        (D.qroot (LocalTheory.sectPlace D.placeSect (c (distinguished (nC D) i))))

Draft theorem:
  theorem leastHull_thetaComponent_eq_pow_floor
      (D : InitialThetaData) (i : Fin (nC D)) (p : Nat.Primes)
      (c : Lab (nC D) i -> LocalTheory.Fiber D.Fmod (.finite p))
      (hbad : (p : Nat) ∈ D.badChars) (hodd : Odd (p : Nat))
      (hunr : forall w : FinitePlace D.Kt, residueChar w = p -> ramIdx D.Kt w = 1) :
      LocalTheory.leastHull (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (D.thetaComponent (nC D) i (.finite p) c) =
      ((p : Nat) : Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)) ^
        (-(Int.floor (ind2Exponent D i p c))) •
      LocalTheory.leastHull (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c))

Proof plan:
1. Rewrite thetaComponent to thetaFiniteOn and thetaFinite_eq:
   thetaFinite = union over phi in indAut/tensorAut of phi '' (scaleElt • shell).
2. Show phi '' (scaleElt • shell) = (phi scaleElt) • shell because tensorAut is a
   group action and phi preserves shell. This needs tensorAut_preserves_shell
   (new, from tensorAut_thetaShell_admissible and factorAut definition).
3. Every phi scaleElt is a unit with the same fractional p-adic valuation modulo Z;
   compute ordp(scaleElt) via ordp_qroot (Data.lean:420) and ordp_pow.
   With hunr, ordp(scaleElt) = ind2Exponent D i p c (or j^2*qOrder/(2*l)).
4. New orbit/rounding lemma:
     exists_tensorAut_scale_min :
       exists phi in tensorAut p c,
         phi '' (scaleElt • shell) =
           p^(-floor x) • leastHull ... shell
   and for every phi, target leastHull is contained in phi '' (scaleElt • shell).
   Proof of the orbit step: tensorAut contains all factor lattice automorphisms; adjust
   each factor by a unit to change the integral part of ordp by any integer, while the
   fractional part floor is fixed; take the componentwise minimum. This is the technical
   heart of the lemma.
5. Apply leastHull_eq/exists_leastHull_eq to the union: the hull of a union whose
   members all contain the same L and include the minimal one is that minimal one.
6. Use mem_smul_archIntegral_iff? No, finite side uses shell/lattice; no arch lemma.
New sublemmas: tensorAut_preserves_shell, tensorAut_action_on_scaleElt,
exists_tensorAut_scale_min, ordp_scaleElt. Mathlib: none beyond Int.floor/zpow algebra.
Status: not immediate; high mathematical risk (the orbit/rounding claim must be checked).

### Lemma 3. leastHull_archLogShell_eq_smul_archIntegral (arch core)

C0 states leastHull = pi^m • archIntegral. This is NOT supported by the source:
- archLogShell is the closed ball of radius pi^m in archTensorCoord
  (archLogShell_eq_preimage, ArchLogShell.lean:285);
- the only source containment is archLogShell_subset (ArchLogShell.lean:374),
  with scalar (sqrt 2 * pi)^m;
- VcI.md:148-154 gives the exact hull scalar sqrt(N) * pi^m, N = 2^(m-1), and
  mu^log(hull) = m log pi + 1/2 log N.
Therefore the plan is to first introduce:
  noncomputable def archHullScale (c : iota -> Place K) : Real :=
    Real.sqrt ((2 : Real) ^ (Fintype.card iota - 1)) * Real.pi ^ Fintype.card iota
and prove:
  theorem leastHull_archLogShell_eq_smul_archIntegral
      (c : iota -> Place K)
      (hc : forall j, (LocalConstruct.archPlace K (c j)).IsComplex) :
      LocalTheory.leastHull .infinite c (LocalTheory.logShell K .infinite c) =
        algebraMap Real (Tensor K .infinite c) (archHullScale c) •
          LocalTheory.integral K .infinite c
If the source/VcI normalization is reconciled differently, replace archHullScale by the
proved scalar; do not assert pi^m.

Proof plan:
1. integral .infinite = archIntegral (rfl; Volume.lean:94-96).
2. Containment: archLogShell subset archHullScale • archIntegral via
   mem_algebraMap_smul_archIntegral; bound each archChar component. Existing
   norm_archChar_sq_le gives norm <= sqrt(2^m) * pi^m = sqrt(2) * archHullScale;
   this is not sharp. New sharper bound norm_archChar_sq_le_N is needed, using
   N = 2^(m-1) complex components and the exact similarity ratio of VcI.md
   (or prove the sharp constant from the tensor basis).
3. Minimality: for any unit a with archLogShell subset a • archIntegral, show every
   archChar radius r_m = |archChar_m a| is at least archHullScale; use
   exists_forall_archChar_eq to put a point on each component boundary and the ball
   geometry; or use the ball's support function. New lemma:
     archHullScale_le_of_subset.
4. leastHull_eq (Gap.lean:97) with a = archHullScale, ha unit, subset, minimality.
New sublemmas: archChar_component_radius_eq, sharp_archChar_bound, archHullScale_le_of_subset.
Status: not immediate; the C0 scalar pi^m must be corrected first.

### Lemma 4. haar_archTensorCoord_eq_smul_lebesgue

Draft theorem:
  theorem haar_archTensorCoord_eq_smul_lebesgue (c : iota -> Place K) :
      exists k : ENNReal, 0 < k ∧ k < top ∧
        Measure.map (archTensorCoord c) (LocalConstruct.haar .infinite c) =
          k • (volume : Measure (EuclideanSpace Real (ArchTensorIdx c)))

Proof plan:
1. archTensorBasis is an orthonormal basis (archTensorInner_basis), so define
   archTensorCoordEquiv : Tensor K .infinite c ~= EuclideanSpace Real (ArchTensorIdx c)
   from archTensorBasis.equivFun and WithLp.linearEquiv; prove it is an isometry
   (norm_archTensorCoord_sq).
2. Pushforward of an addHaar measure under a linear equivalence is addHaar:
   use Measure.addHaar under LinearEquiv (Mathlib Haar/Basic) or prove the translated
   measure is translation-invariant.
3. Uniqueness: addHaarMeasure_unique (Mathlib MeasureTheory/Measure/Haar/Basic.lean)
   on a fixed nonempty compact set (closed unit ball) identifies the pushforward with
   k • volume; k is the ratio of the two measures of the unit ball, positive and finite
   because archLogShell has positive finite measure (haar_archLogShell_pos,
   isCompact_archLogShell.measure_lt_top) and the unit ball is compact nonempty.
4. Optionally compute k from the determinant of archTensorCoordEquiv; determinant is 1
   for an orthonormal basis, so if Haar is normalized to Lebesgue k=1, but do not assume
   this without checking local normalization.
Status: medium; pure measure theory + existing arch basis; writable after ArchLogShell
oleans, no new paper input.

### Lemma 5. Ball and polydisc volumes

Two independent Mathlib-level lemmas:
  theorem volume_archLogShell :
      volume ((archTensorCoord c) '' archLogShell c) =
        (ENNReal.ofReal (Real.pi ^ Fintype.card iota)) ^
          (2 ^ (Fintype.card iota - 1)) * ...Gamma factor...
  theorem volume_archIntegral :
      volume ((archCharLin c) '' archIntegral c) =
        (ENNReal.ofReal Real.pi) ^ (2 ^ (Fintype.card iota - 1))
under hc : all factors complex. The exact gamma form is Mathlib:
  EuclideanSpace.volume_closedBall
    (Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:328)
  with card(ArchTensorIdx)=2^m and radius pi^m;
  Complex.volume_ball / volume_pi for the N complex unit discs.
Proof plan: transport along the linear isometries/equivalences; use Measure.pi_pi /
volume_pi, then evaluate; positivity from pi_pos and positive powers, and
measure_pos of nonempty open sets.
Status: pure Mathlib formulas available; only the identification of
card(ArchTensorIdx) with 2^m (new finrank/card lemma) and the transport maps are lana-side.

### Lemma 6. archDefect_eq

Draft theorem:
  theorem archDefect_eq (c : iota -> Place K)
      (hc : forall j, (LocalConstruct.archPlace K (c j)).IsComplex) :
      LocalTheory.archDefect c =
        Real.log ((Nat.factorial (2 ^ (Fintype.card iota - 1)) : Nat) : Real) /
          (2 * (2 ^ (Fintype.card iota - 1) : Real))
where N = 2^(m-1), 2N = 2^m, matching VcI.md:154.

Proof plan:
1. Use archDefect definition, leastHull_archLogShell_eq_smul_archIntegral (Lemma 3)
   and componentVol_arch_scale to get V(hull) = log(archHullScale).
2. Use Lemma 4 and Lemma 5 to compute
   V(logShell) = (1/d) log(vol_ball/vol_polydisc), d = 2N.
3. Substitute archHullScale = sqrt N * pi^m, vol_ball formula with d=2N,
   vol_polydisc = pi^N; the algebra gives log(N!)/(2N).
4. Verify m=2 gives log2/4 = 0.173286..., matching VcI.md table.
Dependencies: Lemmas 3,4,5 plus componentVol_arch_scale, componentVol_integral.
Status: assembly is straightforward once 3-5 are green; currently blocked by them and
by missing oleans.

## 3. Downstream ind2Term formula (not among the six but the target)

  theorem ind2Term_eq_frac (D) (i) (p) (c) (hbad) (hodd) (hunr) :
      ind2Term D i p c =
        (ind2Exponent D i p c - Int.floor (ind2Exponent D i p c)) * Real.log p
Proof: ind2Term definition; Lemma 2 for Htheta; componentVol_units_smul for
a • leastHull shell (a = scaleElt); componentVol_prod_incl_smul_integral / componentVol
scaling gives V(a • L) = V(L) - x log p; cancel V(L); subtract. The exact sign of
floor follows from x >= 0 (ordp_qroot_nonneg).

## 4. What is immediately writable vs blocked

Immediately writable (signature/skeleton, no new paper input):
- Lemma 1 corollary (componentVol_units_smul_log) — existing source proof.
- Lemma 4 statement + proof outline — Mathlib Haar uniqueness.
- Lemma 5 pure Mathlib ball/polydisc volume formulas.
- Final archDefect_eq statement, with proof depending on 3-5.

Blocked on missing lana oleans (not on TG):
- Every file importing Iut.WallEquiv.Basic/Forms/Gap, Iut.Concrete.LocalConstruct.
  Volume/ScaleVolume/ArchLogShell/Archimedean/IndAut/Theory/LogShell,
  Iut.Concrete.ThetaRegion, Iut.Cor312.Statement, Iut.Wall.IdentifiedCopies.
  Audit: only Iut/Concrete/LocalConstruct/Haar.olean exists (690640 B); all listed
  modules have no .olean in .lake/build/lib/lean/Iut.
- Need mainline/watchdog to build the Iut root first; do not hand-compile.

Mathematically blocked/new estimates:
- Lemma 2: tensorAut orbit/rounding lemma (high risk).
- Lemma 3: exact arch hull scalar; C0 pi^m is wrong; need sharp archChar bound
  or use archHullScale and prove minimality.
- Lemma 6: exact formula is conditional on the scalar reconciliation.

## 5. Recommended write order (after Iut oleans are available)

1. componentVol_units_smul_log (one file, minimal imports).
2. arch measure/ball volume module (Lemmas 4 and 5).
3. archHullScale + Lemma 3 (needs sharp bound; critical path).
4. archDefect_eq (assembly; immediate after 3).
5. ind2Exponent + tensorAut orbit + Lemma 2 (critical path, most mathematical risk).
6. ind2Term_eq_frac (assembly).

No Lean file is written by this plan; no compile is claimed.
