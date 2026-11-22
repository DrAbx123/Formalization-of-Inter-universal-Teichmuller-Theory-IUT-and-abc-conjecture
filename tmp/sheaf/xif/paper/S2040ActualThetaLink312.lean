import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkDisplacementReduction

/-!
# S2040: the actual Theta-link on the actual paper O interface, and the
paper 3.12 inequality

Layer: O (original-text Theta-link / IUT III Corollary 3.12, Step (xi-f)).

This file replaces the placeholder surface S2040ActualThetaLinkActual.lean,
whose S2040ActualThetaLink carries the conclusion
qPilotLogVolume <= signedHullLogVolume as a *field*. Here the conclusion is
derived from actual link data:

* the **real scalar Theta-link** q = Theta^(2l) coming from the paper root
  normalization q[2u] = q[1u]^(1/(2l)) (the paper Theta value is
  q[2u]^(j^2)); the 2l-th root is constructed as a real number and its
  power relation is *proved*, not assumed;
* two **actual Hodge theaters** I.theaterAt 0 0 and I.theaterAt 1 0 and
  their **actual** Hodge-theater/IPL link I.linkAt 0 0 1 0 (this is the
  reduced IUT I Theta-link of the frozen HodgeTheaterLink contract; it is
  not conflated with the log-theta-lattice Theta-link of IUT III);
* the actual **q-pilot / O^×mu link compatibility** data: an actual unit
  equivalence e : U ~= V carrying the root-of-unity subgroup mu <= U onto
  nu <= V (ThetaLinkAssembly.CarriesRootSubgroup), the actual unit-generated
  monoid Theta-link ThetaLinkAssembly.thetaLink, and its
  distinguished-generator law;
* the actual **log-volume / hull comparison**: the paper signed hull
  P.signedHullLogVolume is identified with Real.log Theta (the missing paper
  (xi-d)/(xi-e) hull normalization), from which the inclusion and the paper
  3.12 inequality follow by monotonicity of log on (0,1).

## What is proved unconditionally

* the scalar link q = Theta^(2l) for the constructed Theta = q^(1/(2l));
* 0 < Theta < 1, log Theta < 0, log q = 2l * log Theta;
* log q <= log Theta, hence -|log q| <= -|log Theta| whenever the hull
  normalization identifies P.signedHullLogVolume with log Theta;
* the actual ThetaLinkAssembly link construction and its generator law;
* link_implies_inclusion (the consumer type of
  ThetaLinkActual.link_implies_inclusion) and the paper 3.12 inequality for
  every inhabitant of the actual-link structure S2040ThetaLink312.

## Exact first missing chain (no inhabitant asserted)

1. the four paper q-pilot identifications thetaLinkQPilotPaperIdentifications O
   (strip, arithmetic line bundle, log-Kummer, paper q-log);
2. the q-pilot scalar identification O.qPilotLogVolume = Real.log q;
3. the actual log-theta-lattice Theta-link displacement data
   S2040ThetaLinkDisplacement: the root-stack Theta scalar, the actual
   q-pilot/Theta-pilot strips, the O^×mu unit link, and the actual ambient
   unit-generated monoid link with its degree maps;
4. the paper hull normalization P.signedHullLogVolume = Real.log Theta
   (the paper (xi-d)/(xi-e) procession normalization; in the tree this is
   RootThetaHullNormalizationGap / PaperRootHullFormulaGap).

The S1880/S1905/S1944 reduced routes are not imported and not used: the
q-pilot scalar here is the actual one-column q of the source OriginalInput,
and the signed-hull comparison is derived from the Theta-link root relation,
not from the reduced normalization bound -|log Theta| >= -1.

No sorry, axiom, True/PUnit slot, free comparison field, or arbitrary
inhabitant is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2040ActualThetaLink312

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLink
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume

universe ua uv upi umon uL uC uG uX ulab

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, 0} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip.{umon, uv, upi} V}
variable {X : Type uX} {label : Type ulab} [Fintype label]

/-! ## 1. The real scalar Theta-link q = Theta^(2l) -/

/-- The paper Theta scalar: the real 2l-th root of the q-pilot scalar q[1u].
The paper root is q[2u] = q[1u]^(1/(2l)); here it is realized as the real
root, the only scalar shadow available without the root stack. -/
noncomputable def s2040Theta (l : PrimeGeFive) (q : Real) : Real :=
  q ^ (((2 * l.value : Nat) : Real)⁻¹)

/-- The real 2l-th root is positive for positive q. -/
theorem s2040Theta_pos {q : Real} (hq : 0 < q) :
    0 < s2040Theta l q :=
  Real.rpow_pos_of_pos hq _

/-- The real 2l-th root is below one for 0 < q < 1. -/
theorem s2040Theta_lt_one {q : Real} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    s2040Theta l q < 1 := by
  unfold s2040Theta
  refine Real.rpow_lt_one hq0 hq1 ?_
  have hn : (0 : Real) < ((2 * l.value : Nat) : Real) := by
    exact_mod_cast Nat.mul_pos (by norm_num) l.prime.pos
  exact inv_pos.mpr hn

/-- **The scalar Theta-link**: the 2l-th power of the paper Theta scalar is
the q-pilot scalar. This is the real form of q[1u] = q[2u]^(2l). -/
theorem s2040Theta_pow {q : Real} (hq : 0 ≤ q) :
    s2040Theta l q ^ (2 * l.value) = q := by
  unfold s2040Theta
  refine Real.rpow_inv_natCast_pow hq ?_
  exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero

/-- The logarithm of the Theta scalar. -/
theorem s2040Theta_log {q : Real} (hq : 0 < q) :
    Real.log (s2040Theta l q) =
      (((2 * l.value : Nat) : Real)⁻¹) * Real.log q := by
  unfold s2040Theta
  exact Real.log_rpow hq _

/-- The scalar link in logarithmic form: log q = 2l * log Theta. -/
theorem s2040_log_q_eq_twoL_mul_log_theta {q : Real} (hq : 0 < q) :
    Real.log q = (2 * (l.value : Real)) * Real.log (s2040Theta l q) := by
  rw [s2040Theta_log hq]
  have hl : (0 : Real) < (l.value : Real) := by
    exact_mod_cast l.prime.pos
  have hn : (2 * (l.value : Real)) ≠ 0 := by positivity
  rw [show ((2 * l.value : Nat) : Real) = 2 * (l.value : Real) by
    norm_num [Nat.cast_mul]]
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

/-- The Theta scalar has negative logarithm for a contracting q. -/
theorem s2040_log_theta_neg {q : Real} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.log (s2040Theta l q) < 0 :=
  Real.log_neg (s2040Theta_pos hq0) (s2040Theta_lt_one hq0.le hq1)

/-- **The scalar comparison**: log q <= log Theta. Since q = Theta^(2l),
Theta < 1 and 2l >= 1, the q-pilot signed logarithm is at most the
Theta-pilot signed logarithm. -/
theorem s2040_log_q_le_log_theta {q : Real} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.log q ≤ Real.log (s2040Theta l q) := by
  have hlog : Real.log (s2040Theta l q) < 0 :=
    s2040_log_theta_neg hq0 hq1
  have h2 : (1 : Real) ≤ 2 * (l.value : Real) := by
    have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
    nlinarith
  have hmul : (2 * (l.value : Real)) * Real.log (s2040Theta l q) ≤
      1 * Real.log (s2040Theta l q) :=
    mul_le_mul_of_nonpos_right h2 hlog.le
  rw [one_mul] at hmul
  rw [s2040_log_q_eq_twoL_mul_log_theta hq0]
  exact hmul

/-- The paper signed q-pilot log-volume -|log q| is log q for a contracting
q. -/
theorem s2040_signedLog_eq_log {q : Real} (hq0 : 0 < q) (hq1 : q < 1) :
    -|Real.log q| = Real.log q := by
  rw [abs_of_neg (Real.log_neg hq0 hq1), neg_neg]

/-! ## 2. The S2038 actual paper O interface -/

/-- The S2038 interface: the exact actual paper q-pilot data needed by the
Theta-link. The four paper q-pilot identifications are the exact missing
source obligations, not assumptions proved here. -/
structure S2038PaperOActual
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) where
  /-- The actual paper q-pilot scalar q = q[1u]. -/
  q : Real
  /-- The scalar is the actual one-column q of the source input. -/
  q_eq_source : q = I.oneColumnQAtZero
  q_pos : 0 < q
  /-- The paper q-parameter is contracting (|q| < 1). -/
  q_lt_one : q < 1
  /-- The actual q-pilot prime-strip vertex at (1,0). -/
  qPilotStrip : FPrimeStrip V
  qPilotStrip_eq : qPilotStrip = I.primeStripAt 1 0
  /-- The actual Theta-pilot prime-strip vertex at (0,0). -/
  thetaPilotStrip : FPrimeStrip V
  thetaPilotStrip_eq : thetaPilotStrip = I.primeStripAt 0 0
  /-- The four paper q-pilot identifications (strip, arithmetic line bundle,
  log-Kummer representation, paper q-log scalar). -/
  paperO_identifications : thetaLinkQPilotPaperIdentifications O

/-! ## 3. The actual q-pilot / O^×mu link compatibility -/

/-- The actual O^× -> O^×mu link compatibility: a unit equivalence carrying
the root-of-unity subgroup mu onto nu. This is the actual algebraic data of
the mu_(2l) compatibility; no group is fabricated here. -/
structure S2040UnitsMuLink where
  U : Type
  [groupU : Group U]
  V : Type
  [groupV : Group V]
  /-- The actual unit equivalence of the O^× link. -/
  e : U ≃* V
  /-- The root-of-unity subgroup at the q-pilot. -/
  mu : Subgroup U
  /-- The root-of-unity subgroup at the Theta-pilot. -/
  nu : Subgroup V
  /-- e carries mu onto nu (the mu_(2l) compatibility). -/
  carries_mu : CarriesRootSubgroup e mu nu

attribute [instance] S2040UnitsMuLink.groupU S2040UnitsMuLink.groupV

/-! ## 4. The actual Theta-link displacement data -/

variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}

/-- The actual log-theta-lattice Theta-link displacement between the q-pilot
at (1,0) and the Theta-pilot at (0,0): the root-stack Theta scalar with its
2l-th power relation, the actual strips, the O^×mu unit link, and an actual
unit-generated monoid link built by ThetaLinkAssembly.thetaLink with its
degree maps and generators.

No inhabitant is asserted. The fields are the exact source obligations of
the actual paper Theta-link; the tree constructs only the reduced
HodgeTheaterLink, which preserves q and hence is not this displacement. -/
structure S2040ThetaLinkDisplacement
    (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O)
    where
  /-- The actual O^× -> O^×mu unit link. -/
  unitsMu : S2040UnitsMuLink
  /-- The actual Theta-pilot strip at (0,0). -/
  thetaPilotStrip : FPrimeStrip V
  thetaPilotStrip_eq : thetaPilotStrip = I.primeStripAt 0 0
  /-- The actual q-pilot strip at (1,0). -/
  qPilotStrip : FPrimeStrip V
  qPilotStrip_eq : qPilotStrip = I.primeStripAt 1 0
  /-- The actual root-stack Theta scalar. -/
  rootStackTheta : Real
  rootStackTheta_eq : rootStackTheta = s2040Theta l Opaper.q
  /-- The Theta-link scalar relation q = Theta^(2l). -/
  rootStack_pow : rootStackTheta ^ (2 * l.value) = Opaper.q
  /-- The q-side ambient value group. -/
  ambientQ : Type
  [commGroupQ : CommGroup ambientQ]
  /-- The Theta-side ambient value group. -/
  ambientTheta : Type
  [commGroupTheta : CommGroup ambientTheta]
  /-- The q-side unit embedding. -/
  embedQ : unitsMu.U →* ambientQ
  /-- The Theta-side unit embedding. -/
  embedTheta : unitsMu.V →* ambientTheta
  /-- The q-side integer degree for the unit-generated monoid link. -/
  intDegreeQ : ambientQ →* Multiplicative Int
  /-- The Theta-side integer degree for the unit-generated monoid link. -/
  intDegreeTheta : ambientTheta →* Multiplicative Int
  /-- The q-side real log-degree (the actual log-volume readout). -/
  logDegreeQ : ambientQ →* Multiplicative Real
  /-- The Theta-side real log-degree (the actual log-volume readout). -/
  logDegreeTheta : ambientTheta →* Multiplicative Real
  injQ : Function.Injective embedQ
  injTheta : Function.Injective embedTheta
  unitDegreeQ : ∀ a : unitsMu.U, intDegreeQ (embedQ a) = 1
  unitDegreeTheta : ∀ b : unitsMu.V, intDegreeTheta (embedTheta b) = 1
  /-- The q-pilot generator. -/
  generatorQ : ambientQ
  /-- The Theta-pilot generator. -/
  generatorTheta : ambientTheta
  generatorQ_logDegree : (logDegreeQ generatorQ).toAdd = Real.log Opaper.q
  generatorTheta_logDegree :
    (logDegreeTheta generatorTheta).toAdd = Real.log rootStackTheta
  generatorQ_degree_ne_zero : (intDegreeQ generatorQ).toAdd ≠ 0
  generatorTheta_degree_ne_zero : (intDegreeTheta generatorTheta).toAdd ≠ 0

attribute [instance] S2040ThetaLinkDisplacement.commGroupQ
  S2040ThetaLinkDisplacement.commGroupTheta

namespace S2040ThetaLinkDisplacement

variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
  (Label := Label) (Choice := Choice) (l := l) (V := V) O}

/-- **The actual unit-generated monoid Theta-link.** This is the actual
ThetaLinkAssembly.thetaLink for the displacement data, with the actual unit
equivalence e and the actual generators/degrees. -/
noncomputable def thetaLink (D : S2040ThetaLinkDisplacement Opaper) :
    unitGeneratedSubmonoid D.embedQ D.generatorQ ≃*
      unitGeneratedSubmonoid D.embedTheta D.generatorTheta :=
  LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly.thetaLink
    (u := D.embedQ) (v := D.embedTheta) (q := D.generatorQ)
    (theta := D.generatorTheta) (degreeG := D.intDegreeQ)
    (degreeH := D.intDegreeTheta) (hu := D.injQ) (hv := D.injTheta)
    (hunitG := D.unitDegreeQ) (hunitH := D.unitDegreeTheta)
    (hq := D.generatorQ_degree_ne_zero)
    (htheta := D.generatorTheta_degree_ne_zero) (e := D.unitsMu.e)

/-- The actual link sends the q-pilot distinguished generator to the
Theta-pilot distinguished generator. This is the q-pilot / O^×mu generator
compatibility of the link. -/
theorem thetaLink_generator (D : S2040ThetaLinkDisplacement Opaper) :
    D.thetaLink (distinguishedGenerator D.embedQ D.generatorQ) =
      distinguishedGenerator D.embedTheta D.generatorTheta :=
  LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly.thetaLink_generator
    (u := D.embedQ) (v := D.embedTheta) (q := D.generatorQ)
    (theta := D.generatorTheta) (degreeG := D.intDegreeQ)
    (degreeH := D.intDegreeTheta) (hu := D.injQ) (hv := D.injTheta)
    (hunitG := D.unitDegreeQ) (hunitH := D.unitDegreeTheta)
    (hq := D.generatorQ_degree_ne_zero)
    (htheta := D.generatorTheta_degree_ne_zero) (e := D.unitsMu.e)

/-- The actual link is compatible with the root-of-unity subgroups: the image
of the source squared-label orbit is the target squared-label orbit. -/
theorem thetaLink_squaredLabelOrbit (D : S2040ThetaLinkDisplacement Opaper)
    (j : SignedLabel l.value) :
    D.thetaLink ''
        sourceSquaredLabelOrbit (u := D.embedQ) (q := D.generatorQ)
          (mu := D.unitsMu.mu) (j := j.1) =
      targetSquaredLabelOrbit (v := D.embedTheta) (theta := D.generatorTheta)
        (nu := D.unitsMu.nu) (j := j.1) :=
  LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly.thetaLink_image_sourceSquaredLabelOrbit
    (u := D.embedQ) (v := D.embedTheta) (q := D.generatorQ)
    (theta := D.generatorTheta) (degreeG := D.intDegreeQ)
    (degreeH := D.intDegreeTheta) (hu := D.injQ) (hv := D.injTheta)
    (hunitG := D.unitDegreeQ) (hunitH := D.unitDegreeTheta)
    (hq := D.generatorQ_degree_ne_zero)
    (htheta := D.generatorTheta_degree_ne_zero) (e := D.unitsMu.e)
    (mu := D.unitsMu.mu) (nu := D.unitsMu.nu)
    (he := D.unitsMu.carries_mu) (j := j.1)

end S2040ThetaLinkDisplacement

/-! ## 5. The actual paper Theta-link and its derived inclusion -/

/-- **The actual paper Theta-link on the S2038 O interface.** It carries the
two actual Hodge theaters I.theaterAt 0 0 and I.theaterAt 1 0 with their
actual HodgeTheaterLink, the actual Theta-link displacement data, the q-pilot
scalar identification, and the actual paper hull normalization. The inclusion
and the 3.12 inequality are *not* fields. -/
structure S2040ThetaLink312
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O)
    (P : PaperSignedHull X label) where
  /-- The actual Hodge-theater link between the two actual theaters (0,0)
  and (1,0). This is the actual IPL/Hodge-theater link; it is not the
  log-theta-lattice Theta-link, whose displacement is the next field. -/
  theaterLink : HodgeTheaterLink (I.theaterAt 0 0) (I.theaterAt 1 0)
  theaterLink_eq : theaterLink = I.linkAt 0 0 1 0
  /-- The actual log-theta-lattice Theta-link displacement. -/
  displacement : S2040ThetaLinkDisplacement Opaper
  /-- The paper q-log identification: the object q-pilot scalar is log q. -/
  qPilotLogIdentification : O.qPilotLogVolume = Real.log Opaper.q
  /-- The actual paper hull normalization -|log Theta| = log Theta. -/
  hull_normalization : P.signedHullLogVolume =
    Real.log displacement.rootStackTheta

namespace S2040ThetaLink312

variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
  (Label := Label) (Choice := Choice) (l := l) (V := V) O}
variable {P : PaperSignedHull X label}

/-- The q-pilot scalar of the actual link is the paper signed -|log q|. -/
theorem qPilotLogVolume_eq_neg_abs (L : S2040ThetaLink312 O Opaper P) :
    O.qPilotLogVolume = -|Real.log Opaper.q| := by
  rw [L.qPilotLogIdentification,
    s2040_signedLog_eq_log Opaper.q_pos Opaper.q_lt_one]

/-- **The first milestone: link_implies_inclusion.** The actual Theta-link
implies that the q-pilot scalar lies in the paper ray R_{<= -|log Theta|}.
This is the consumer type of ThetaLinkActual.link_implies_inclusion; here it
is proved, not assumed. -/
theorem link_implies_inclusion (L : S2040ThetaLink312 O Opaper P) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume := by
  rw [mem_hullLogVolumeRay_iff]
  rw [L.qPilotLogIdentification, L.hull_normalization]
  have h := s2040_log_q_le_log_theta (l := l) Opaper.q_pos Opaper.q_lt_one
  simpa [L.displacement.rootStackTheta_eq] using h

/-- **The actual paper 3.12 inequality** -|log q| <= -|log Theta|. -/
theorem paper312_inequality (L : S2040ThetaLink312 O Opaper P) :
    -|Real.log Opaper.q| ≤ P.signedHullLogVolume := by
  rw [← qPilotLogVolume_eq_neg_abs L]
  exact (mem_hullLogVolumeRay_iff).mp L.link_implies_inclusion

/-- The same inequality in the paper q-pilot scalar form. -/
theorem paper312_inequality_qPilot (L : S2040ThetaLink312 O Opaper P) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp L.link_implies_inclusion

/-- The signed-hull comparison is exactly the ray membership. -/
theorem paper312_iff_ray (L : S2040ThetaLink312 O Opaper P) :
    (-|Real.log Opaper.q| ∈ hullLogVolumeRay P.signedHullLogVolume) ↔
      -|Real.log Opaper.q| ≤ P.signedHullLogVolume :=
  mem_hullLogVolumeRay_iff

/-- The Theta-link root relation gives the positive magnitude form
|log Theta| = (1/(2l)) |log q|. -/
theorem log_theta_abs_eq (L : S2040ThetaLink312 O Opaper P) :
    |Real.log L.displacement.rootStackTheta| =
      (((2 * l.value : Nat) : Real)⁻¹) * |Real.log Opaper.q| := by
  rw [L.displacement.rootStackTheta_eq, s2040Theta_log Opaper.q_pos, abs_mul,
    abs_of_pos (inv_pos.mpr (by
      exact_mod_cast Nat.mul_pos (by norm_num) l.prime.pos))]

end S2040ThetaLink312

/-! ## 6. The exact first-missing chain -/

/-- The q-pilot scalar identification: the actual paper q-pilot scalar is
log q (equivalently -|log q|). This is part of the paper q-log
identification; it is not proved from the bare PaperQPilotObject. -/
def S2040QPilotLogIdentification
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O) : Prop :=
  O.qPilotLogVolume = Real.log Opaper.q

/-- The actual paper hull normalization: the signed hull log-volume is
log Theta for the Theta-link Theta scalar. This is the paper (xi-d)/(xi-e)
procession-normalization identification at the actual hull; in the tree it is
RootThetaHullNormalizationGap / PaperRootHullFormulaGap, not a free
parameter. -/
def S2040HullNormalization
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O)
    (P : PaperSignedHull X label)
    (D : S2040ThetaLinkDisplacement Opaper) : Prop :=
  P.signedHullLogVolume = Real.log D.rootStackTheta

/-- The exact first-missing chain of the actual paper Theta-link:
(1) the four paper q-pilot identifications, (2) the q-pilot scalar
identification, (3) the actual Theta-link displacement data, and (4) the
actual paper hull normalization.

No inhabitant is asserted, and none of the components is a renamed target:
the components are object-level identifications/constructions, and the
inclusion and the 3.12 inequality are proved from them below. -/
def S2040FirstMissing
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O)
    (P : PaperSignedHull X label) : Prop :=
  thetaLinkQPilotPaperIdentifications O ∧
    S2040QPilotLogIdentification O Opaper ∧
    ∃ D : S2040ThetaLinkDisplacement Opaper,
      S2040HullNormalization Opaper P D

/-- From the exact first-missing chain one obtains the actual Theta-link. -/
theorem s2040ThetaLink312_of_firstMissing
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O}
    {P : PaperSignedHull X label}
    (M : S2040FirstMissing O Opaper P) :
    Nonempty (S2040ThetaLink312 O Opaper P) := by
  obtain ⟨_hpaper, hq, D, hhull⟩ := M
  exact ⟨{ theaterLink := I.linkAt 0 0 1 0
           theaterLink_eq := rfl
           displacement := D
           qPilotLogIdentification := hq
           hull_normalization := hhull }⟩

/-- The first-missing chain implies the paper inclusion. -/
theorem s2040_inclusion_of_firstMissing
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O}
    {P : PaperSignedHull X label}
    (M : S2040FirstMissing O Opaper P) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume := by
  obtain ⟨L⟩ := s2040ThetaLink312_of_firstMissing M
  exact L.link_implies_inclusion

/-- The first-missing chain implies the actual paper 3.12 inequality. -/
theorem s2040_paper312_of_firstMissing
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O}
    {P : PaperSignedHull X label}
    (M : S2040FirstMissing O Opaper P) :
    -|Real.log Opaper.q| ≤ P.signedHullLogVolume := by
  obtain ⟨L⟩ := s2040ThetaLink312_of_firstMissing M
  exact L.paper312_inequality

/-- The first-missing chain is exactly: paper O identifications, q-pilot log
identification, an actual displacement datum, and its hull normalization. -/
theorem s2040FirstMissing_iff
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O}
    {P : PaperSignedHull X label} :
    S2040FirstMissing O Opaper P ↔
      thetaLinkQPilotPaperIdentifications O ∧
        S2040QPilotLogIdentification O Opaper ∧
        ∃ D : S2040ThetaLinkDisplacement Opaper,
          S2040HullNormalization Opaper P D :=
  Iff.rfl

/-! ## 7. Axiom probes -/

#print axioms s2040Theta_pow
#print axioms s2040_log_q_eq_twoL_mul_log_theta
#print axioms s2040_log_q_le_log_theta
#print axioms S2040ThetaLinkDisplacement.thetaLink
#print axioms S2040ThetaLinkDisplacement.thetaLink_generator
#print axioms S2040ThetaLinkDisplacement.thetaLink_squaredLabelOrbit
#print axioms S2040ThetaLink312.link_implies_inclusion
#print axioms S2040ThetaLink312.paper312_inequality
#print axioms s2040ThetaLink312_of_firstMissing
#print axioms s2040_paper312_of_firstMissing

end LeanFormal.IUT.XiFPaper.S2040ActualThetaLink312
end
