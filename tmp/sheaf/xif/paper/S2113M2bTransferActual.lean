import tmp.sheaf.xif.paper.S2098M2aCoreActual
import Brauer.ArtinTransfer

/-!
# S2113: M2b (norm/transfer compatibility) -- the Brauer port, the Galois-side
normalisation, and the exact missing Verlagerung comparison

Layer: **O** (original Theta-link / q-pilot).  Consumers: S2024's
LocalReciprocityData.transfer_compat, S2098's
localReciprocityData_of_source, S2027's localReciprocityData_of_source,
and through them S2017's muQZComparison / muHatComparison.

## What the Brauer port supplies

The ported local CFT library now contains
PadicField.artin_transfer (Brauer/ArtinTransfer.lean):

  for K' : IntermediateField K Omega and a : K^x, every lift
  g : Gal(Omega/K) of artin_K(a) satisfies
  artin_{K'}(a) = ver p K' g.

This file applies it to the **fixed-field extension** L_H / L_K
(H <= K open subgroups of G_v = Gal(Qbar_p/Q_p)), namely to
K' = FH H h, the intermediate field FixedField H regarded over
FixedField K.  The resulting theorem artinTransfer_fixedField is the
norm side of (M2b): the reciprocity map sends the inclusion of roots of
unity to the transfer.

## What is unconditionally proved here

* localArtinTorsionEquiv_apply: the actual M2a torsion equivalence of
  S2098 is exactly the Artin map on roots of unity,
  localArtinTorsionEquiv U z = galoisGroupEquiv U (artin z).
  (This is a real computation through galoisGroupMaximalAbelianEquivProd,
  PadicField.galAbEquiv and galAbEquiv_symm_apply.)

* galoisGroupMaximalAbelian_mk and galoisGroupEquiv_restrictNormalHom:
  the canonical map Ab U -> Gal(maximalAbelianExtension U / L_U),
  kappa U = galoisGroupMaximalAbelian U o abelianizationToTopological U,
  acts on Abelianization.of k by restricting the automorphism
  localGaloisGroupEquiv U k to the maximal abelian extension, and this
  restriction is compatible with S2089's galoisGroupEquiv.

* artinTransfer_fixedField: the ported norm/transfer theorem specialised
  to the fixed-field extension.  No sorry, no new axiom.

## The exact first missing API

S2024's transfer_compat (and S2098's
localReciprocityTransferCompatibility) compare the **abstract**
Verlagerung

  verlagerungOpen h : Abelianization K ->* Abelianization H

with the **Galois** transfer PadicField.ver p (FH H h).  The port proves
the latter is the norm on reciprocity, but there is no API identifying the
two transfers on the torsion carriers.  In this file that identification is
the named proposition TransferBridge (stated on the Galois carriers
torsion (Abelianization U) and Gal(maximalAbelianExtension U / L_U)).
It is *not* assumed, not an axiom, and not inhabited; it is the precise
first missing input.  The theorem
canonicalTransferCompat_of_transferBridge shows that exactly this bridge
yields the canonical transfer square, hence S2024's datum, once the
abstract-vs-profinite carrier comparison (M2c) is available.

There is a second, purely definitional carrier gap.  PadicField.ver is
stated for K' : IntermediateField K Omega, so artinTransfer_fixedField lands
in Gal(PadicField.maxAbelian (↥(FH H h)) / ↥(FH H h)), whereas S2027's carrier
is Gal(maximalAbelianExtension H / localField H).  The two fields have the
same underlying subset of Qbar_p but different Algebra instances; no lemma in
the tree identifies the two Galois groups or transports PadicField.ver.  This
is the second exact missing API (VerCarrierComparison below).

A third, definitional obstruction in S2098 is the use of
(hc U).some for an arbitrary hc : forall U, Nonempty (...): the extracted
equivalence is not the canonical map.  localArtinSourceDataOfCanonical
below therefore uses the canonical carrier explicitly.  This is a
replacement of the Classical.choice interface, not a mathematical input.

## Not run

Full Project build, target comparator, independent review.  The file itself
is compiled by lake env lean; the axiom probes at the end show only
propext, Classical.choice, Quot.sound.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual
open LeanFormal.IUT.XiFPaper.S2098M2aCoreActual
open IntermediateField

namespace LeanFormal.IUT.XiFPaper.S2113M2bTransferActual

variable {p : Nat} [Fact (Nat.Prime p)]

/-! ## 1. The fixed-field extension and the ported transfer theorem -/

/-- FixedField H regarded as an intermediate field over
FixedField K, for H <= K.  The carrier is literally the fixed field of
H; the base is the fixed field of K. -/
noncomputable def FH {K : Index p} (H : Index p) (h : H ≤ K) :
    IntermediateField (localField p K) (AlgebraicClosure ℚ_[p]) where
  toSubalgebra :=
    { carrier := (LocalIntegralUnitKummerInjectivity.FixedField p H :
        Set (AlgebraicClosure ℚ_[p]))
      zero_mem' := (LocalIntegralUnitKummerInjectivity.FixedField p H).zero_mem
      add_mem' := fun hx hy =>
        IntermediateField.add_mem (LocalIntegralUnitKummerInjectivity.FixedField p H) hx hy
      mul_mem' := fun hx hy =>
        IntermediateField.mul_mem (LocalIntegralUnitKummerInjectivity.FixedField p H) hx hy
      algebraMap_mem' := fun (x : localField p K) => by
        change (x : AlgebraicClosure ℚ_[p]) ∈
          LocalIntegralUnitKummerInjectivity.FixedField p H
        exact fixedField_le h x.2
      one_mem' := (LocalIntegralUnitKummerInjectivity.FixedField p H).one_mem }
  inv_mem' := fun (x : AlgebraicClosure ℚ_[p])
    (hx : x ∈ LocalIntegralUnitKummerInjectivity.FixedField p H) =>
    IntermediateField.inv_mem (LocalIntegralUnitKummerInjectivity.FixedField p H) hx

/-- FixedField H is finite over FixedField K. -/
instance FH_finiteDimensional {K : Index p} (H : Index p) (h : H ≤ K) :
    FiniteDimensional (localField p K) (FH H h) := by
  haveI : Module.Finite ℚ_[p] (FH H h) := by
    change Module.Finite ℚ_[p] (localField p H)
    infer_instance
  exact Module.Finite.of_restrictScalars_finite ℚ_[p] (localField p K) (FH H h)

/-- **The ported norm/transfer theorem on the fixed-field extension.**
For H <= K, a root of unity y of L_K and a lift g of artin_K(y),
the Artin map of the inclusion L_K <= L_H is the Verlagerung of g. -/
theorem artinTransfer_fixedField {H K : Index p} (h : H ≤ K) (y : mu p K)
    (g : localGaloisGroup p K)
    (hg : AlgEquiv.restrictNormalHom
        (PadicField.maxAbelian (localField p K) (AlgebraicClosure ℚ_[p])) g =
      PadicField.artin p (localField p K) (AlgebraicClosure ℚ_[p]) y) :
    PadicField.artin p (↥(FH H h)) (AlgebraicClosure ℚ_[p])
      (Units.map (algebraMap (localField p K) (↥(FH H h))) (y : (localField p K)ˣ)) =
      PadicField.ver p (FH H h) g :=
  PadicField.artin_transfer (p := p) (K := localField p K)
    (Ω := AlgebraicClosure ℚ_[p]) (K' := FH H h) y g hg

/-! ## 2. The Artin computation of the torsion equivalence -/

/-- The underlying element of (torsionMulEquiv e).symm y is e.symm y. -/
theorem torsionMulEquiv_symm_coe {A B : Type*} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (y : CommGroup.torsion B) :
    (((torsionMulEquiv e).symm y : CommGroup.torsion A) : A) = e.symm (y : B) := rfl

/-- The underlying element of (torsionProdOfRightTorsionFree h).symm y is
(y, 1). -/
theorem torsionProdOfRightTorsionFree_symm_coe {A B : Type*} [CommGroup A] [CommGroup B]
    (hB : ∀ b : B, IsOfFinOrder b → b = 1) (y : CommGroup.torsion A) :
    (((torsionProdOfRightTorsionFree hB).symm y :
      CommGroup.torsion (A × B)) : A × B) = ((y : A), 1) := rfl

/-- The underlying unit of (torsionUnitGroupEquivMu U).symm z is z. -/
theorem torsionUnitGroupEquivMu_symm_coe (U : Index p) (z : mu p U) :
    (((torsionUnitGroupEquivMu U).symm z :
      CommGroup.torsion (PadicField.unitGroup p (localField p U))) :
      PadicField.unitGroup p (localField p U)) = ⟨(z : (localField p U)ˣ), by
        exact PadicField.mem_unitGroup.mpr
          (nrm_coe_eq_one_of_isOfFinOrder U ((CommGroup.mem_torsion _).mp z.2))⟩ := by
  apply Subtype.ext
  rfl

/-- galAbEquiv.symm (u, 1) = artin u. -/
theorem galAbEquiv_symm_unit_apply (U : Index p)
    (u : PadicField.unitGroup p (localField p U)) :
    (PadicField.galAbEquiv p (localField p U) (AlgebraicClosure ℚ_[p])
        (uniformizerUnit_val U)).symm (u, 1) =
      PadicField.artin p (localField p U) (AlgebraicClosure ℚ_[p])
        (u : (localField p U)ˣ) := by
  rw [PadicField.galAbEquiv_symm_apply]
  simp

/-- **The actual M2a torsion equivalence is the Artin map on roots of
unity.**  This is the computation of localArtinTorsionEquiv through
galoisGroupMaximalAbelianEquivProd and PadicField.galAbEquiv. -/
theorem localArtinTorsionEquiv_apply (U : Index p) (z : mu p U) :
    localArtinTorsionEquiv U z =
      galoisGroupEquiv U
        (PadicField.artin p (localField p U) (AlgebraicClosure ℚ_[p]) z) := by
  unfold localArtinTorsionEquiv
  simp only [MulEquiv.trans_apply]
  rw [torsionMulEquiv_symm_coe]
  rw [torsionProdOfRightTorsionFree_symm_coe]
  rw [torsionUnitGroupEquivMu_symm_coe]
  rw [galoisGroupMaximalAbelianEquivProd]
  rw [MulEquiv.symm_trans_apply]
  rw [MulEquiv.symm_symm]
  apply_fun (galoisGroupEquiv U).symm
  simp only [MulEquiv.symm_apply_apply]
  trans (PadicField.artin p (localField p U) (AlgebraicClosure ℚ_[p])
        (z : (localField p U)ˣ)) *
      (PadicField.artinZHat p (localField p U) (AlgebraicClosure ℚ_[p])
        (uniformizerUnit U)) 1
  · exact PadicField.galAbEquiv_symm_apply (p := p) (K := localField p U)
      (Ω := AlgebraicClosure ℚ_[p]) (hπ := uniformizerUnit_val U)
      (x := ((⟨(z : (localField p U)ˣ), by
        exact PadicField.mem_unitGroup.mpr
          (nrm_coe_eq_one_of_isOfFinOrder U ((CommGroup.mem_torsion _).mp z.2))⟩ :
        PadicField.unitGroup p (localField p U)), 1))
  · simp

/-! ## 3. The canonical map from the abstract to the Galois abelianization -/

/-- Gal(maximalAbelianExtension U / L_U) is normal over L_U. -/
instance maximalAbelianExtension_normal (U : Index p) :
    Normal (localField p U) (maximalAbelianExtension p U) := by
  haveI hfix : (maximalAbelianExtension p U).fixingSubgroup.Normal := by
    rw [fixingSubgroup_maximalAbelianExtension p U]
    exact commutatorClosed_normal p U
  exact ((InfiniteGalois.normal_iff_isGalois
    (maximalAbelianExtension p U)).mp hfix).to_normal

/-- The reverse field equivalence acts as the identity on underlying
elements. -/
theorem maxAbelianEquiv_symm_apply (U : Index p)
    (y : maximalAbelianExtension p U) :
    (((maxAbelianEquivMaximalAbelianExtension U).symm y :
      PadicField.maxAbelian (localField p U) (AlgebraicClosure ℚ_[p])) :
      AlgebraicClosure ℚ_[p]) = (y : AlgebraicClosure ℚ_[p]) := rfl

/-- **The maximal-abelian quotient computes the restriction map.** -/
theorem galoisGroupMaximalAbelian_mk (U : Index p)
    (g : localGaloisGroup p U) :
    galoisGroupMaximalAbelian p U
      (QuotientGroup.mk'
        ((commutator (localGaloisGroup p U)).topologicalClosure) g) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension p U) g := by
  change (InfiniteGalois.normalAutEquivQuotient (commutatorClosed p U))
      (QuotientGroup.mk' (commutatorClosed p U).1 g) = _
  ext z
  rfl

/-- **S2089's galoisGroupEquiv commutes with restriction to the maximal
abelian extension.** -/
theorem galoisGroupEquiv_restrictNormalHom (U : Index p)
    (g : localGaloisGroup p U) :
    galoisGroupEquiv U
        (AlgEquiv.restrictNormalHom
          (PadicField.maxAbelian (localField p U) (AlgebraicClosure ℚ_[p])) g) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension p U) g := by
  ext y
  rw [galoisGroupEquiv_apply]
  rw [maxAbelianEquivMaximalAbelianExtension_apply]
  rw [AlgEquiv.restrictNormalHom_apply]
  rw [maxAbelianEquiv_symm_apply]
  rw [AlgEquiv.restrictNormalHom_apply]

/-- The canonical map Ab U -> Gal(maximalAbelianExtension U / L_U), i.e.
the topological abelianization followed by the maximal-abelian quotient. -/
noncomputable def kappa (U : Index p) :
    Abelianization ↥U →*
      Gal(↥(maximalAbelianExtension p U) / localField p U) :=
  (galoisGroupMaximalAbelian p U).toMonoidHom.comp
    (abelianizationToTopological p U)

/-- kappa on a generator is restriction of the corresponding Galois
automorphism. -/
theorem kappa_of (U : Index p) (k : ↥U) :
    kappa U (Abelianization.of k) =
      galoisGroupEquiv U
        (AlgEquiv.restrictNormalHom
          (PadicField.maxAbelian (localField p U) (AlgebraicClosure ℚ_[p]))
          (localGaloisGroupEquiv p U k)) := by
  unfold kappa
  rw [MonoidHom.comp_apply]
  rw [show abelianizationToTopological p U (Abelianization.of k) =
      QuotientGroup.mk'
        ((commutator (localGaloisGroup p U)).topologicalClosure)
        (localGaloisGroupEquiv p U k) from rfl]
  change galoisGroupMaximalAbelian p U
      (QuotientGroup.mk'
        ((commutator (localGaloisGroup p U)).topologicalClosure)
        (localGaloisGroupEquiv p U k)) = _
  rw [galoisGroupMaximalAbelian_mk]
  rw [galoisGroupEquiv_restrictNormalHom]

/-- The torsion comparison map tau U = galoisGroupMaximalAbelian U. -/
theorem tau_canonical (U : Index p) (v : CommGroup.torsion (Abelianization ↥U)) :
    torsionMulEquiv (galoisGroupMaximalAbelian p U)
        (torsionMap (abelianizationToTopological p U) v) =
      torsionMap (kappa U) v := by
  apply Subtype.ext
  rfl

/-- The inverse of localArtinSourceArtin is tau followed by the inverse
of localArtinTorsionEquiv. -/
theorem localArtinSourceArtin_symm_apply (U : Index p)
    (y : CommGroup.torsion
      (TopologicalAbelianization (localGaloisGroup p U))) :
    (localArtinSourceArtin U).symm y =
      (localArtinTorsionEquiv U).symm
        (torsionMulEquiv (galoisGroupMaximalAbelian p U) y) := by
  unfold localArtinSourceArtin
  rw [MulEquiv.symm_trans_apply]
  rfl

/-! ## 4. The canonical levelwise equivalence and the transfer square -/

/-- The canonical homomorphism from the abstract abelianization to the
profinite abelianization on torsion. -/
noncomputable def canonicalCarrier (U : Index p)
    (h : canonicalTorsionComparison p U) :
    CommGroup.torsion (Abelianization ↥U) ≃*
      CommGroup.torsion
        (TopologicalAbelianization (localGaloisGroup p U)) :=
  MulEquiv.ofBijective (torsionMap (abelianizationToTopological p U)) h

/-- The canonical levelwise equivalence torsion (Ab U) ~= mu U, assuming
the abstract-vs-profinite carrier comparison (M2c) at U. -/
noncomputable def canonicalEquiv (U : Index p)
    (h : canonicalTorsionComparison p U) :
    CommGroup.torsion (Abelianization ↥U) ≃* mu p U :=
  (canonicalCarrier U h).trans (localArtinSourceArtin U).symm

/-- Computation rule for the canonical equivalence. -/
theorem canonicalEquiv_apply (U : Index p)
    (h : canonicalTorsionComparison p U)
    (v : CommGroup.torsion (Abelianization ↥U)) :
    canonicalEquiv U h v =
      (localArtinTorsionEquiv U).symm (torsionMap (kappa U) v) := by
  unfold canonicalEquiv canonicalCarrier
  rw [MulEquiv.trans_apply]
  rw [MulEquiv.ofBijective_apply]
  rw [localArtinSourceArtin_symm_apply]
  rw [tau_canonical]

/-- **The missing carrier comparison.**  The PadicField maximal-abelian
carrier for the intermediate field `FH H h` and S2027's carrier for the fixed
field of `H` are the same subfield of `Qbar_p`, but are built with different
`Algebra` instances.  No lemma in the tree identifies the two Galois groups;
this is the precise carrier-level missing API. -/
def VerCarrierComparison : Prop :=
  ∀ {H K : Index p} (h : H ≤ K),
    Nonempty
      (Gal(↥(PadicField.maxAbelian (↥(FH H h)) (AlgebraicClosure ℚ_[p])) / ↥(FH H h)) ≃*
        Gal(↥(maximalAbelianExtension p H) / localField p H))

/-- **The exact missing comparison (M2b-bridge).**  The abstract
Verlagerung on the torsion abelianizations, transported to the Galois
carriers by kappa, is the norm/Artin transfer on the roots of unity.
This is *not* assumed anywhere as an axiom; it is the named gap left after
the port. -/
def TransferBridge : Prop :=
  ∀ {H K : Index p} (h : H ≤ K)
    (v : CommGroup.torsion (Abelianization K)),
    torsionMap (kappa H) (torsionMap (verlagerungOpen p h) v) =
      localArtinTorsionEquiv H
        (fixedFieldTorsionUnitsInclusion p h
          ((localArtinTorsionEquiv K).symm (torsionMap (kappa K) v)))

/-- The canonical transfer square, in the form consumed by S2024/S2027. -/
def CanonicalTransferCompat
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U) : Prop :=
  ∀ {H K : Index p} (h : H ≤ K)
    (v : CommGroup.torsion (Abelianization K)),
    canonicalEquiv H (hM2c H) (torsionMap (verlagerungOpen p h) v) =
      fixedFieldTorsionUnitsInclusion p h
        (canonicalEquiv K (hM2c K) v)

/-- **The bridge implies the canonical transfer square.** -/
theorem canonicalTransferCompat_of_transferBridge
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U)
    (hbridge : TransferBridge (p := p)) :
    CanonicalTransferCompat (p := p) hM2c := by
  intro H K h v
  rw [canonicalEquiv_apply, canonicalEquiv_apply]
  rw [hbridge h v]
  rw [MulEquiv.symm_apply_apply]

/-! ## 5. The canonical source datum and S2027/S2098 consumers -/

/-- The source datum with the canonical carrier, avoiding the
Classical.choice in S2098's localArtinSourceDataOfComparison. -/
noncomputable def localArtinSourceDataOfCanonical
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U) :
    LocalArtinSourceData p where
  artin := fun U => localArtinSourceArtin U
  carrier := fun U => canonicalCarrier U (hM2c U)

/-- The levelwiseEquiv of the canonical datum is canonicalEquiv. -/
theorem levelwiseEquiv_canonical (hM2c : ∀ U : Index p,
      canonicalTorsionComparison p U) (U : Index p) :
    levelwiseEquiv p (localArtinSourceDataOfCanonical hM2c) U =
      canonicalEquiv U (hM2c U) := rfl

/-- The canonical transfer square is exactly S2027's htransfer hypothesis
for the canonical source datum. -/
theorem canonicalTransferCompat_iff_source
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U) :
    CanonicalTransferCompat (p := p) hM2c ↔
      ∀ {H K : Index p} (h : H ≤ K)
        (v : CommGroup.torsion (Abelianization K)),
        levelwiseEquiv p (localArtinSourceDataOfCanonical hM2c) H
            (torsionMap (verlagerungOpen p h) v) =
          fixedFieldTorsionUnitsInclusion p h
            (levelwiseEquiv p (localArtinSourceDataOfCanonical hM2c) K v) := by
  constructor <;> intro h H K hh v
  · simpa only [levelwiseEquiv_canonical] using h hh v
  · simpa only [levelwiseEquiv_canonical] using h hh v

/-- **M2c + the transfer bridge give S2024's datum.** -/
noncomputable def localReciprocityData_of_canonical
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U)
    (hbridge : TransferBridge (p := p)) :
    LocalReciprocityData p :=
  S2027LocalArtinActual.localReciprocityData_of_source p
    (localArtinSourceDataOfCanonical hM2c)
    ((canonicalTransferCompat_iff_source hM2c).mp
      (canonicalTransferCompat_of_transferBridge hM2c hbridge))

/-- **M2c + the transfer bridge give S2017's muQZComparison.** -/
theorem muQZComparison_of_canonical
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U)
    (hbridge : TransferBridge (p := p)) :
    muQZComparison p :=
  muQZComparison_of_data p (localReciprocityData_of_canonical hM2c hbridge)

/-- **M2c + the transfer bridge give S2017's muHatComparison.** -/
theorem muHatComparison_of_canonical
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U)
    (hbridge : TransferBridge (p := p)) :
    muHatComparison p :=
  muHatComparison_of_data p (localReciprocityData_of_canonical hM2c hbridge)

/-! ## 6. The literal S2098 interface and the `.some` obstruction -/

/-- If the arbitrary `Nonempty` witness used by S2098 is the canonical carrier,
then its `levelwiseEquiv` is the canonical one. -/
theorem levelwiseEquiv_ofComparison_eq_canonical
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U)
    (hc : localArtinSourceCarrierMissing (p := p))
    (hcanon : ∀ U : Index p,
      (hc U).some = canonicalCarrier U (hM2c U)) (U : Index p) :
    levelwiseEquiv p (localArtinSourceDataOfComparison hc) U =
      canonicalEquiv U (hM2c U) := by
  unfold levelwiseEquiv canonicalEquiv localArtinSourceDataOfComparison
  change ((hc U).some).trans (localArtinSourceArtin U).symm =
    (canonicalCarrier U (hM2c U)).trans (localArtinSourceArtin U).symm
  rw [hcanon U]

/-- **S2098's `localReciprocityTransferCompatibility` from the canonical
transfer bridge and the identification of the chosen carrier.**  The
hypothesis `hcanon` is exactly the `.some` obstruction: S2098 extracts an
arbitrary equivalence from `Nonempty`, and the canonical square only controls
the canonical map. -/
theorem localReciprocityTransferCompatibility_of_canonical
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U)
    (hc : localArtinSourceCarrierMissing (p := p))
    (hcanon : ∀ U : Index p,
      (hc U).some = canonicalCarrier U (hM2c U))
    (hbridge : TransferBridge (p := p)) :
    localReciprocityTransferCompatibility (p := p) hc := by
  intro H K h v
  rw [levelwiseEquiv_ofComparison_eq_canonical hM2c hc hcanon H,
    levelwiseEquiv_ofComparison_eq_canonical hM2c hc hcanon K]
  exact canonicalTransferCompat_of_transferBridge hM2c hbridge h v

/-- **Literal S2098 consumer.**  With the canonical carrier chosen and the
transfer bridge, S2098's `localReciprocityData_of_source` produces S2024's
datum. -/
noncomputable def localReciprocityData_of_source_canonical
    (hM2c : ∀ U : Index p, canonicalTorsionComparison p U)
    (hc : localArtinSourceCarrierMissing (p := p))
    (hcanon : ∀ U : Index p,
      (hc U).some = canonicalCarrier U (hM2c U))
    (hbridge : TransferBridge (p := p)) :
    LocalReciprocityData p :=
  S2098M2aCoreActual.localReciprocityData_of_source hc
    (localReciprocityTransferCompatibility_of_canonical hM2c hc hcanon hbridge)

/-! ## 7. Axiom probes -/

#print axioms artinTransfer_fixedField
#print axioms localArtinTorsionEquiv_apply
#print axioms galoisGroupMaximalAbelian_mk
#print axioms galoisGroupEquiv_restrictNormalHom
#print axioms kappa_of
#print axioms canonicalEquiv_apply
#print axioms canonicalTransferCompat_of_transferBridge
#print axioms localReciprocityData_of_canonical
#print axioms localReciprocityTransferCompatibility_of_canonical
#print axioms localReciprocityData_of_source_canonical
#print axioms muQZComparison_of_canonical
#print axioms muHatComparison_of_canonical

end LeanFormal.IUT.XiFPaper.S2113M2bTransferActual

end