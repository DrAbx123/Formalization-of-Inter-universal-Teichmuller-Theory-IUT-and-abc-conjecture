import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTII.Kummer.SourceThetaPilotIQContainment
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# Mzk1IQThetaPilotImageActual — literal-object θ-pilot image `n,◦U_{vQ}` and hull map

A481 task (theta side): construct, on the LITERAL carriers, the θ-pilot image of the
IQ-carrier local factor `n,◦U_{vQ}` and the concrete hull map.  Inputs (existing assets):
* `ThetaLinkAssembly`: θ-link `u * qbar^n |-> e(u) * Theta^n` and its evaluated orbits
  (`sourceEvaluationOrbit`, `targetEvaluationOrbit`, squared-label orbits);
* `SourceThetaPilotIQContainment`: the one-place tensor packet and the reduced tensor
  IQ submodule `sourceThetaPilotIQPacket`, plus the orbit-containment lemma;
* `FiniteThetaPacket`: the finite real theta packet `q`, `scale j = q^(j^2)` and its
  log-volume;
* `SourceLogShellCarrier`: the literal local log-shell datum `D` with `D.Units`, `D.K`,
  `D.unitLayer`, `D.preLogShell`, `D.logShell` and `logMap_pow_val`.

Nothing here uses a model/value-realized carrier or an abstract interface: the n-th
unit-power image is defined on `D.Units`, its log image on `D.K`, and the θ-pilot orbits
on the monoid `unitGeneratedSubmonoid`.  No sorry/axiom. Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1IQThetaPilotImageActual

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
open LeanFormal.IUT.SourceLogShellDatum
open scoped BigOperators

/-! ## 1. θ-pilot image of the evaluated n-th unit orbit (`n,◦U_{vQ}` orbit) -/

section ThetaLinkImage

variable {U V G H : Type*} [Group U] [Group V] [CommGroup G] [CommGroup H]
variable (u : U →* G) (v : V →* H) (q : G) (theta : H)
variable (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
variable (hu : Function.Injective u) (hv : Function.Injective v)
variable (hunitG : ∀ a, degreeG (u a) = 1)
variable (hunitH : ∀ b, degreeH (v b) = 1)
variable (hq : (degreeG q).toAdd ≠ 0)
variable (htheta : (degreeH theta).toAdd ≠ 0)

/-- The literal θ-pilot image of the n-th evaluated unit orbit (the paper's local
`n,◦U_{vQ}` orbit) on the target generated monoid: the θ-link image of
`sourceEvaluationOrbit mu n`. -/
noncomputable def iqThetaPilotNImage (e : U ≃* V) (mu : Subgroup U) (n : ℕ) :
    Set (unitGeneratedSubmonoid v theta) :=
  thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e ''
    sourceEvaluationOrbit u q mu n

/-- The θ-pilot n-th-unit image is literally the target evaluated orbit, when the unit
equivalence carries the root subgroup (θ-link synchronization theorem). -/
theorem iqThetaPilotNImage_eq_target (e : U ≃* V) (mu : Subgroup U) (nu : Subgroup V)
    (he : CarriesRootSubgroup e mu nu) (n : ℕ) :
    iqThetaPilotNImage u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e mu n =
      targetEvaluationOrbit v theta nu n :=
  thetaLink_image_sourceEvaluationOrbit u v q theta degreeG degreeH hu hv hunitG hunitH
    hq htheta e mu nu he n

/-- Membership form: every source n-th unit power maps to an element of the target
θ-pilot n-th-unit image. -/
theorem unitPowerElement_mem_iqThetaPilotNImage (e : U ≃* V) (mu : Subgroup U)
    {zeta : U} (hz : zeta ∈ mu) (n : ℕ) :
    unitPowerElement v theta (e zeta) n ∈
      iqThetaPilotNImage u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e mu n :=
  ⟨unitPowerElement u q zeta n, ⟨zeta, hz, rfl⟩,
    thetaLink_unitPower u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e zeta n⟩

/-- Source hull: union of the squared-label evaluation orbits `mu * qbar^(j^2)`. -/
noncomputable def sourceThetaPilotHullSet (mu : Subgroup U) (J : Type*) (label : J → ℤ) :
    Set (unitGeneratedSubmonoid u q) :=
  ⋃ j : J, sourceSquaredLabelOrbit u q mu (label j)

/-- Target hull image: union of the target squared-label orbits `nu * Theta^(j^2)`. -/
noncomputable def iqThetaPilotHullImage (nu : Subgroup V) (J : Type*) (label : J → ℤ) :
    Set (unitGeneratedSubmonoid v theta) :=
  ⋃ j : J, targetSquaredLabelOrbit v theta nu (label j)

/-- The θ-link carries the whole source hull onto the target hull image (concrete hull
map, label family arbitrary). -/
theorem thetaLink_image_sourceHull (e : U ≃* V) (mu : Subgroup U) (nu : Subgroup V)
    (he : CarriesRootSubgroup e mu nu) (J : Type*) (label : J → ℤ) :
    thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e ''
        sourceThetaPilotHullSet u q mu J label =
      iqThetaPilotHullImage v theta nu J label := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [sourceThetaPilotHullSet] at hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [← thetaLink_image_sourceSquaredLabelOrbit u v q theta degreeG degreeH hu hv
      hunitG hunitH hq htheta e mu nu he (label j)]
    exact Set.mem_image_of_mem _ hxj
  · intro hy
    rw [iqThetaPilotHullImage] at hy
    rcases Set.mem_iUnion.mp hy with ⟨j, hyj⟩
    rw [← thetaLink_image_sourceSquaredLabelOrbit u v q theta degreeG degreeH hu hv
      hunitG hunitH hq htheta e mu nu he (label j)] at hyj
    rcases hyj with ⟨x, hx, rfl⟩
    exact ⟨x, Set.mem_iUnion.mpr ⟨j, hx⟩, rfl⟩

/-- Membership of a squared-label target orbit element in the hull image. -/
theorem unitPowerElement_mem_iqThetaPilotHullImage (nu : Subgroup V)
    (J : Type*) (label : J → ℤ) (j : J) {zeta : V} (hz : zeta ∈ nu) :
    unitPowerElement v theta zeta (Int.toNat (label j * label j)) ∈
      iqThetaPilotHullImage v theta nu J label :=
  Set.mem_iUnion.mpr ⟨j, ⟨zeta, hz, rfl⟩⟩

end ThetaLinkImage

/-! ## 2. The literal local factor `n,◦U_{vQ}` on the source log-shell datum -/

section LocalIQCarrier

variable {D : SourceLogShellDatum}

/-- The literal n-th power unit image `n,◦U_{vQ}` of a local source log-shell datum,
as a subset of its log-coordinate field `D.K`: the log images of `u^n`, `u ∈ D.Units`. -/
def nU_vQImage (D : SourceLogShellDatum) (n : ℕ) : Set D.K :=
  {a | ∃ u : D.Units, (D.logMap (u ^ n)).toAdd = a}

/-- `n,◦U_{vQ}` is exactly the n-times-scalar image of the unit layer in log
coordinates. -/
theorem nU_vQImage_eq (D : SourceLogShellDatum) (n : ℕ) :
    nU_vQImage D n = {a : D.K | ∃ b : D.K, b ∈ D.unitLayer ∧ a = n • b} := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(D.logMap u).toAdd, ⟨u, rfl⟩, logMap_pow_val D u n⟩
  · rintro ⟨b, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, logMap_pow_val D u n⟩

/-- The literal n-th unit image maps into the pre-log-shell whenever the unit layer
does (the local-factor hull containment). -/
theorem nU_vQImage_subset_preLogShell (D : SourceLogShellDatum) (n : ℕ)
    (h : D.unitLayer ⊆ D.preLogShell) : nU_vQImage D n ⊆ D.preLogShell := by
  intro a ha
  rw [nU_vQImage_eq] at ha
  rcases ha with ⟨b, hb, rfl⟩
  have hb' : b ∈ D.preLogShell := h hb
  induction n with
  | zero =>
      simpa using zero_mem_preLogShell D
  | succ n ih =>
      rw [succ_nsmul]
      exact add_mem_preLogShell D ih hb'

/-- The zero element is in the literal n-th power unit image (via `u = 1`). -/
theorem zero_mem_nU_vQImage (D : SourceLogShellDatum) (n : ℕ) :
    (0 : D.K) ∈ nU_vQImage D n := by
  refine ⟨1, ?_⟩
  rw [logMap_pow_val D 1 n, map_one]
  simp

end LocalIQCarrier

/-! ## 3. Finite theta packet: concrete θ-pilot image and hull map (real log coordinates) -/

section FinitePacket


/-- The concrete θ-pilot n-th image of a finite theta packet: the n-th powers of the
actual Gaussian special values `scale j = q^(j^2)`. -/
def finitePacketThetaPilotImage {l : PrimeGeFive} (packet : FiniteThetaPacket l) (n : ℕ) :
    Set Real := {t | ∃ j : SignedLabel l.value, t = packet.scale j ^ n}

/-- Every packet scale power lies in the concrete θ-pilot image. -/
theorem scale_pow_mem_finitePacketThetaPilotImage {l : PrimeGeFive}
    (packet : FiniteThetaPacket l) (j : SignedLabel l.value) (n : ℕ) :
    packet.scale j ^ n ∈ finitePacketThetaPilotImage packet n :=
  ⟨j, rfl⟩

/-- The concrete θ-pilot image consists of strictly positive reals. -/
theorem finitePacketThetaPilotImage_pos {l : PrimeGeFive}
    (packet : FiniteThetaPacket l) (n : ℕ) :
    ∀ t ∈ finitePacketThetaPilotImage packet n, 0 < t := by
  rintro t ⟨j, rfl⟩
  exact pow_pos (packet.scale_pos j) n

/-- The concrete hull map: the log-volume ray built from the packet's log-scales. -/
def finitePacketHullMap {l : PrimeGeFive} (packet : FiniteThetaPacket l) (n : ℕ) :
    Set Real := {t | ∃ j : SignedLabel l.value, t = n * Real.log (packet.scale j)}

/-- The hull map is the log of the concrete θ-pilot image. -/
theorem finitePacketHullMap_eq_log_image {l : PrimeGeFive}
    (packet : FiniteThetaPacket l) (n : ℕ) :
    finitePacketHullMap packet n =
      {t : Real | ∃ j : SignedLabel l.value, t = Real.log (packet.scale j ^ n)} := by
  ext t
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, (Real.log_pow (packet.scale j) n).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, Real.log_pow (packet.scale j) n⟩

/-- Packet log-scales lie in the hull map at n = 1. -/
theorem log_scale_mem_finitePacketHullMap_one {l : PrimeGeFive}
    (packet : FiniteThetaPacket l) (j : SignedLabel l.value) :
    Real.log (packet.scale j) ∈ finitePacketHullMap packet 1 :=
  ⟨j, by ring⟩

end FinitePacket

/-! ## 4. IQ-carrier side: the n-th unit orbit is stable inside the literal IQ submodule -/

section IQCarrier

universe uK uM

open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer

variable {l : PrimeGeFive} {G : LGPMonoid.{uM} l}
variable {D : SourceLogShellDatum.{uK}} {j : Nat}
variable {P : LGPMonoidAction G Rat (sourceLogShellOnePlaceFamily D j)}

/-- The `n,◦U_{vQ}` orbit action (splitting-monoid scalar action) preserves the literal
one-place source tensor IQ submodule. -/
theorem splittingAction_mem_sourceThetaPilotIQPacket (T : ThetaPilotObject P ())
    {g : G.Carrier} (hg : g ∈ G.splittingMonoid)
    {x : TensorPacket (sourceLogShellOnePlaceFamily D j) ()}
    (hx : x ∈ sourceThetaPilotIQPacket D j) :
    (LGPMonoidAction.actionOnTensorPacket P () g x) ∈ sourceThetaPilotIQPacket D j := by
  rw [LGPMonoidAction.actionOnTensorPacket_apply]
  exact (sourceThetaPilotIQPacket D j).smul_mem (P.scalar g) hx

/-- The literal IQ carrier contains the whole θ-pilot possible image once it contains
the generator (orbit-containment consumer on the literal packet). -/
theorem thetaPilot_IQImage_subset (T : ThetaPilotObject P ())
    (hgen : T.generator ∈ sourceThetaPilotIQPacket D j) :
    T.possibleImage ⊆ sourceThetaPilotIQPacket D j :=
  possibleImage_subset_sourceThetaPilotIQPacket T hgen

end IQCarrier

#check iqThetaPilotNImage_eq_target
#check thetaLink_image_sourceHull
#check nU_vQImage_eq
#check nU_vQImage_subset_preLogShell
#check finitePacketHullMap_eq_log_image
#check splittingAction_mem_sourceThetaPilotIQPacket

end LeanFormal.IUT.XiFPaper.Mzk1IQThetaPilotImageActual
end
