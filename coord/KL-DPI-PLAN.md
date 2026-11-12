# KL-DPI-PLAN — Mathlib KL chain rule, DPI draft, and theta/q Haar mapping

Status: READ-ONLY plan, 2026-11-12. No Lean file written, no compile.
Source: Mathlib.InformationTheory.KullbackLeibler.ChainRule (Mathlib v4.32.2).
Classification per A1067: TOOL only; this is NOT our variant and NOT lana SSIneq.

## 1. Exact Mathlib facts

From Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:

  variable {X Y : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
    {mu nu : Measure X} {kappa eta : Kernel X Y}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    [IsMarkovKernel kappa] [IsMarkovKernel eta]

  theorem klDiv_compProd_eq_add :
    klDiv (mu compProd kappa) (nu compProd eta)
      = klDiv mu nu + klDiv (mu compProd kappa) (mu compProd eta)

  @[simp] lemma klDiv_compProd_left :
    klDiv (mu compProd kappa) (nu compProd kappa) = klDiv mu nu

The theorem has no absolute-continuity/integrability hypotheses; those are
handled inside the if-then-else definition of klDiv. The composition product is
Measure.compProd, written in Lean with the Unicode tensor notation (import
Mathlib.Probability.Kernel.Composition.MeasureCompProd).

## 2. Lean DPI draft

  import Mathlib.InformationTheory.KullbackLeibler.ChainRule

  open MeasureTheory ProbabilityTheory InformationTheory
  open scoped ENNReal

  variable {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    {mu nu : Measure alpha} {kappa eta : Kernel alpha beta}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    [IsMarkovKernel kappa] [IsMarkovKernel eta]

  /-- Data-processing inequality for a pair of Markov kernels, from the KL
  chain rule and nonnegativity of the conditional KL. -/
  theorem klDiv_le_compProd :
      klDiv mu nu <= klDiv (mu compProd kappa) (nu compProd eta) := by
    rw [klDiv_compProd_eq_add]
    exact le_add_right le_rfl

  /-- Same-channel specialization: equality (DPI is tight for identical
  post-processing). -/
  theorem klDiv_compProd_same :
      klDiv (mu compProd kappa) (nu compProd kappa) = klDiv mu nu :=
    klDiv_compProd_left

Notes for compilation:
- klDiv is in namespace InformationTheory (open it).
- compProd requires Mathlib.Probability.Kernel.Composition.MeasureCompProd; it
  is imported by ChainRule.
- The inequality uses ENNReal addition; le_add_right le_rfl gives
  klDiv mu nu <= klDiv mu nu + conditional-KL.
- No extra [SigmaFinite] hypotheses are needed beyond the finite-measure and
  Markov-kernel typeclasses used in ChainRule.

## 3. Mapping to theta/q-pilot normalized Haar restrictions

Target data we would need (none of this exists yet as a single API):

(1) Measure spaces:
  X := C3LogShellTensorBlock C3
  mu_theta := normalized restriction of actualC3LogShellTensorHaar to
    actualC3LogShellTensorRegion C3
  nu_q := normalized restriction of the same Haar to qPilotHaarRegion C3
  (assuming the q-side region exists; currently GAP).

A normalized restriction must be defined as a finite measure. For a finite
positive measure lam on X and measurable S with 0 < lam S < top:
  normalizedRestriction lam S := (lam S).toReal⁻¹ • lam.restrict S
(a probability measure on X; a subtype version is also possible). We need:
  - measurableRegion predicates,
  - positivity/finiteness fields,
  - finite-measure instances for the normalized restrictions.

(2) Channels:
  kappa : Kernel X (Fin k) a deterministic component/projection kernel, e.g.
    kappa x = Measure.dirac (componentLabel x)
  for a measurable component label (bad-place/tensor coordinate).
  eta : a second coarsening/refinement kernel (e.g. forget some components).
  Both are Markov kernels if componentLabel is measurable.

(3) KL object:
  klDiv mu_theta nu_q is a relative-entropy quantity between normalized
  restrictions. For nested regions A subset B and restrictions of the same
  Haar, klDiv(mu|A, mu|B) = log (mu B / mu A) (when finite/positive); for
  non-nested regions it is an integral of the log density ratio.

(4) DPI direction:
  klDiv mu_theta nu_q <= klDiv (mu_theta compProd kappa) (nu_q compProd eta).
  This says coarsening cannot increase distinguishability. It gives a LOWER
  bound on the joint KL from the marginal KL, or an UPPER bound on the marginal
  from the joint (if the joint is controlled). It does not directly give
  log mu_theta <=/>= log mu_q.

## 4. What DPI can and cannot do for our variant

Our target is the weaker variant:
  V + gap - (sF - 1) * A >= 0, i.e. M = A - R >= 0, i.e. -A <= rhs.
DPI on normalized restrictions yields statements about
  log (mu(qRegion) / mu(thetaRegion))
or about relative entropy, not about the signed log-volume inequality.
In the nested case theta subset q (the direction needed for negHaarLog),
  log mu(q) - log mu(theta) >= 0
is automatic monotonicity; DPI adds no new sign. It could be used only as:
- a diagnostic that a proposed component approximation loses at most a
  controlled KL amount;
- a way to compare two different coarsenings of the same volume profile;
not as a proof of M >= 0.

Therefore DPI is a TOOL for error/approximation control, not a replacement for
  - qPilotHaarRegion and qPilotLogVolume = -haarLogVolume,
  - thetaRegion subset qPilotRegion,
  - the CTheta/hscalar and N5 lower-bound inputs.

## 5. Minimal new declarations for a real Lean instantiation

1. normalizedRestriction (finite measure) and its finite-measure instance.
2. componentLabel : C3LogShellTensorBlock C3 -> Fin k, measurable.
3. componentKernel := deterministic kernel from componentLabel.
4. qPilotHaarRegion and theta region measurability/positivity/finiteness
   (currently GAP; required before any KL statement).
5. A theorem relating klDiv of normalized restrictions to log-volume ratios
   (needed only if one wants to translate the KL inequality into volume terms).
6. No new axiom and no lana SSIneq; all steps are TOOL.

## 6. Verdict

- The DPI Lean draft is immediately formalizable from Mathlib; no new
  information-theory API is needed.
- The hard part is the volume mapping: normalized Haar restrictions and the
  q-pilot region do not yet exist; theta/q regions are GAP, so klDiv cannot be
  instantiated on them today.
- Even after instantiation, DPI gives a relative-entropy inequality, not the
  signed log-volume comparison or our variant. It should be used only as a
  diagnostic/approximation tool.
- Strong-inequality classification: TOOL; do not encode lana SSIneq/Wall/Thm311/
  Cor312Variant through a KL shortcut.
- No Lean file written; no compile claimed.
