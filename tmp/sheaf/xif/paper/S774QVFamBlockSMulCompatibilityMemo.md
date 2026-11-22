# S774: QVFamBlockSMulCompatibility — Mathlib/tool memo (Task U)

Date: 2026-10-30. Scope: research + small compile experiments. No changes to
paper statements or consumers.

## Verdict

* Do NOT reject the target. QVFamBlockSMulCompatibility is true and already
  has an actual proof in
  tmp/sheaf/xif/paper/S741QVFamBlockSMulActual.lean
  (qVFamBlockSMulCompatibility_actual).
* No new instance needs to be invented. Mathlib already supplies the exact
  generic interface: LinearMap.CompatibleSMul, the instance
  LinearMap.IsScalarTower.compatibleSMul, and the lemma
  LinearMap.map_smul_of_tower.
* Two verified tactic routes are recorded below. Route A is the reusable
  Mathlib route; Route B is the already-landed S741 proof.
* Axiom status of both the S741 theorem and the Route A probe theorem:
  [propext, Classical.choice, Quot.sound]. No sorryAx, no extra axiom.

## Target

S730QVFamBlockLatticeAlignmentActual.lean:32 defines

    def QVFamBlockSMulCompatibility : Prop :=
      forall (z : Z_p[qVFamTensorP T b]) (x : qVFamTensorBlock T b),
        qVFamBlockLinearEquiv T b (z • x) =
          z • qVFamBlockLinearEquiv T b x

It is a Prop, not a class, so there is no single pre-existing instance with
that name. The useful question is which scalar-tower / CompatibleSMul
instance proves it, and that is answered below.

## Ready-made Mathlib tools

* Mathlib/Algebra/Module/LinearMap/Defs.lean:353
  class LinearMap.CompatibleSMul (R S) [Semiring S] [SMul R M]
    [Module S M] [SMul R M2] [Module S M2] : Prop
  with field map_smul : forall (f : M →_l[S] M2) (c : R) (x : M),
    f (c • x) = c • f x.
* Same file, line 364:
  instance (priority := 100) LinearMap.IsScalarTower.compatibleSMul
    [SMul R S] [IsScalarTower R S M] [IsScalarTower R S M2] :
    CompatibleSMul M M2 R S
* Same file, line 374:
  LinearMap.map_smul_of_tower [CompatibleSMul M M2 R S]
    (f : M →_l[S] M2) (c : R) (x : M) : f (c • x) = c • f x
  and line 378: LinearMapClass.map_smul_of_tower for bundled maps.
* Mathlib/Algebra/Group/Action/Defs.lean:566:
  smul_one_smul (N) [IsScalarTower M N α] (x : M) (y : α) :
    (x • (1 : N)) • y = x • y
  This is the rewrite used inside the proof of the Mathlib instance.
* Mathlib/Algebra/Algebra/RestrictScalars.lean:220:
  Algebra.restrictScalars R S A = Algebra.compHom A (algebraMap R S),
  i.e. its smul is definitionally (algebraMap R S r) • x.

## Project instances already available

* Scoped: LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegralLattice.lean
  - line 25: scoped instance padicIntegerModule : Module Z_p M
    (Module.compHom M (algebraMap Z_p Q_p));
  - line 30: padicInteger_smul_eq (z) (x) : z • x = (z : Q_p) • x, proved by rfl;
  - line 32: scoped instance padicIntegerScalarTower :
    IsScalarTower Z_p Q_p M.
  These are scoped: the file must open scoped
  LeanFormal.IUT.FinitePadicIntegralLattice to activate them.
* Global: LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceHolomorphicIntegralClosure.lean
  - line 49: instance arithmeticTensorTupleZpAlgebra :
    Algebra Z_p (ArithmeticTensorTupleBlock places tuple)
    (defined as Algebra.restrictScalars Z_p Q_p _);
  - line 55: instance arithmeticTensorTupleZpIsScalarTower :
    IsScalarTower Z_p Q_p (ArithmeticTensorTupleBlock places tuple).
  qVFamTensorBlock T b is an abbrev for ArithmeticTensorTupleBlock, so these
  apply directly to the tensor side. They are global (not scoped).
* Global: LeanFormal/IUT/Foundations/LocalFields/IntegralTraceDualTensorInclusion.lean:580
  instance localFieldZpAlgebra : Algebra Z_p L
  for every proper complete ultrametric normed field L over Q_p.
  rootBase T b = NormalizedCompletion (qVFamTensorPlace T b) satisfies all
  the assumptions, so rootBase gets this global Algebra Z_p instance too.
* Mathlib/NumberTheory/Padics/PadicIntegers.lean:557:
  instance algebra : Algebra Z_p Q_p, supplying the SMul Z_p Q_p used by
  IsScalarTower.
* FinitePlaceRelativeNormalizedCompletion.lean:20 and :24 record that the
  Module Q_p from NormedSpace and the Module Q_p from the Algebra structure
  on CommonPrimeCompletion have the same toSMul (proved by rfl). This is the
  alignment that lets the Z_p action be read as the Q_p action.

## Route A (recommended, verified)

Proof shape (verified in tmp/_probe_qvfam_smul_compat.lean, exit 0):

    theorem qVFamBlockSMulCompatibility_compatibleSMul_route :
        QVFamBlockSMulCompatibility (l := l) T b := by
      haveI : IsScalarTower ℤ_[qVFamTensorP T b] ℚ_[qVFamTensorP T b] (rootBase T b) :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      haveI : LinearMap.CompatibleSMul (qVFamTensorBlock T b) (rootBase T b)
          ℤ_[qVFamTensorP T b] ℚ_[qVFamTensorP T b] :=
        LinearMap.IsScalarTower.compatibleSMul
      intro z x
      exact LinearMap.map_smul_of_tower
        (qVFamBlockLinearEquiv (l := l) T b).toLinearMap z x

Why it works:
* the tensor side already has the global Algebra Z_p + IsScalarTower
  instances from FinitePlaceHolomorphicIntegralClosure;
* the rootBase side gets Algebra Z_p from localFieldZpAlgebra; since that is
  Algebra.restrictScalars, the tower is exactly
  IsScalarTower.of_algebraMap_eq (fun _ => rfl);
* LinearMap.IsScalarTower.compatibleSMul then synthesizes the instance;
* LinearMap.map_smul_of_tower is precisely the goal after intro z x.

Observed axioms of the probe theorem:
  [propext, Classical.choice, Quot.sound].

## Route B (already landed in S741, verified)

    theorem qVFamBlockSMulCompatibility_actual :
        QVFamBlockSMulCompatibility (l := l) T b := by
      intro z x
      rw [LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq,
        LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq,
        map_smul]

Verified: lake env lean -j1 -R . -o ... S741QVFamBlockSMulActual.lean
exits 0. The Route A probe also prints the axioms of this S741 theorem:
[propext, Classical.choice, Quot.sound].

Subtle point: this works because the scoped Module.compHom action and the
global Algebra.restrictScalars action have the same underlying smul
(both are (algebraMap Z_p Q_p z) • x). The two padicInteger_smul_eq
rewrites normalize the tensor-side and rootBase-side actions to the Q_p
action, and then the Q_p-linear qVFamBlockLinearEquiv.map_smul closes the
goal. Do not read this as a general fact that any two Module Z_p instances
are interchangeable; the alignment here is definitional.

## Route C (fallback, verified on a Mathlib-only toy)

    rw [← smul_one_smul ℚ_[qVFamTensorP T b] z x,
        ← smul_one_smul ℚ_[qVFamTensorP T b] z
          (qVFamBlockLinearEquiv (l := l) T b x),
        map_smul]

This also avoids CompatibleSMul and only needs the two IsScalarTower
instances. It was compiled in tmp/_probe_smul_tower.lean (exit 0) for an
abstract pair M, N; it is a valid fallback if the CompatibleSMul instance
search is inconvenient.

## Actual consumer in the tree

tmp/sheaf/xif/paper/S772QVFamBlockMapsLatticeActual.lean (created by the
parallel QVFamBlock worker) already imports S741 and uses the theorem in the
span induction step:

    rw [show qVFamBlockLinearEquiv (l := l) T b (z • x) =
        z • qVFamBlockLinearEquiv (l := l) T b x from
      qVFamBlockSMulCompatibility_actual (l := l) T b z x]
    exact Submodule.smul_mem _ z hx

So the Zp-smul step of the QVFamBlockMapsFractionalLattice span induction is
now discharged; the remaining exact hypothesis there is the pure-tensor
image statement S772PureTensorGoal (not part of Task U).

## Rejections / cautions

* Do not reject QVFamBlockSMulCompatibility: it is true and proved.
* Do not try to prove it from Algebra.smul_def alone by pushing through the
  tensor algebra multiplication; qVFamBlockLinearEquiv is only Q_p-linear,
  not multiplicative. The S724 memo's failure of a direct Algebra.smul_def
  rewrite is explained by the scoped/global instance mismatch, not by a
  false target.
* Do not add a new axiom/opaque instance. No new assumption is needed.
* If a downstream file uses the scoped padicIntegerModule, it must open
  scoped LeanFormal.IUT.FinitePadicIntegralLattice. If it uses the global
  Algebra Z_p instances instead, no scope is needed. Both routes are
  actual, but do not mix a rewrite lemma stated for one instance with an
  occurrence elaborated under the other without a defeq check.

## Evidence / commands

* S741 direct compile:
    lake env lean -j1 -R . -o
      .lake/build/lib/lean/tmp/sheaf/xif/paper/S741QVFamBlockSMulActual.olean
      tmp/sheaf/xif/paper/S741QVFamBlockSMulActual.lean
  exit 0; olean produced.
* Probe Route A:
    lake env lean -j1 -R . -o .lake/build/lib/lean/tmp/_probe_qvfam_smul_compat.olean
      tmp/_probe_qvfam_smul_compat.lean
  exit 0; both #print axioms lines show the three standard axioms.
* Toy Route C: lake env lean -j1 tmp/_probe_smul_tower.lean, exit 0.
* The first lean_auto audit of S741 was blocked before compilation by a
  stale dependency (IntegralLogShellIndexResidueFormula source newer than
  its olean). That module was rebuilt green with
    python -X utf8 -B tools/lean_auto.py build
      LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
  (Build completed successfully, 3614 jobs). Lake's incremental build did
  not rewrite that olean's mtime, so a second lean_auto audit still reported
  stale_dependency and also inputs_changed from concurrent workspace edits.
  A direct recompile
    lake env lean -j1 -R . -o
      .lake/build/lib/lean/LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellIndexResidueFormula.olean
      LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellIndexResidueFormula.lean
  then exited 0 and refreshed the olean (mtime 2026-10-30 01:38:39).
  A final lean_auto audit was then run and returned GREEN:
    status green, exit 0, stale_modules [], errors [], forbidden [],
    source_count 9050,
    log tmp/lean-automation/build-e0c8c04afee9497aa5284aa793151d6c.log
    (cmd exit=0 total=102.1s).
  Validation scope is local compilation + lexical policy, not an axiom audit
  or a paper-faithfulness audit; the axiom print above is separate.

## Remaining verification status

* statement_compiles: yes for S741 and Route A probe.
* proof_body_checked: yes, direct Lean exit 0 for both; no sorry/admit.
* kernel_closed: yes for the printed declarations; axioms are the three
  standard ones. This is a local declaration check, not a full project
  build or paper-faithfulness audit.
* lean_auto audit: GREEN for S741 (status green, exit 0, no errors, no
  forbidden tokens; source_count 9050). This is local compilation + lexical
  policy only, not a full project build or paper-faithfulness audit.
* target_accepted: no. The consumer chain (QVFamBlockMapsFractionalLattice
  span induction, S720/S724) is outside this task and still needs its own
  integration check.
