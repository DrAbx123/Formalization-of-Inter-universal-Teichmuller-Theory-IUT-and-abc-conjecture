
/-! ## 2. Component (a): the actual F-double-plus-prime-strip -/

/-- The actual tempered and etale fundamental-group data of the once-punctured
elliptic curve at a place, as required by IUT II, Definition 1.1 and
Example 1.8.  The curve is the actual affine curve curveScheme Q_v, card is the
certified etale fundamental group of its finite etale covers (the frozen source
card CurveEtaleFundamentalGroupCard), tempered is the tempered fundamental
group, and the projection onto the actual local absolute Galois group has
nontrivial geometric kernel. -/
structure CurvePiOneData (v : PaperV) where
  curve : Scheme
  curve_eq : curve = curveScheme ℚ_[v.1]
  card : CurveEtaleFundamentalGroupCard ℚ_[v.1]
  tempered : Type
  [groupTempered : Group tempered]
  [topTempered : TopologicalSpace tempered]
  comparison : tempered →* (card.fundamentalGroup : Type)
  proj : tempered →* @LocalAbsoluteGalois v.1 ⟨v.prime⟩
  proj_surjective : Function.Surjective proj
  geometric_nontrivial : Nontrivial proj.ker

/-- (a) The paper actual F-double-plus-prime-strip: the local O-times monoids of
the actual local fields, the actual once-punctured elliptic curves with their
tempered/etale fundamental groups, and the functorial surjections with
nontrivial geometric kernels. -/
structure FPsiPrimeStrip (l : PrimeGeFive) where
  strip : FPrimeStrip PaperV
  mon_eq : ∀ v : PaperV, strip.Mon v = LocalOFieldUnitsAt v
  g_eq : ∀ v : PaperV, strip.G v = @LocalAbsoluteGalois v.1 ⟨v.prime⟩
  piOne : (v : PaperV) → CurvePiOneData v
  pi_eq : ∀ v : PaperV, strip.Pi v = (piOne v).tempered
  geometric_nontrivial :
    ∀ v : PaperV, Nontrivial (DPrimeStrip.geometric strip.toDPrimeStrip v)

/-- Every subgroup with a nontrivial carrier is a nontrivial subgroup. -/
theorem ne_bot_of_nontrivial {G : Type*} [Group G] {H : Subgroup G}
    (h : Nontrivial H) : H ≠ ⊥ := by
  intro hbot
  obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
  apply hxy
  apply Subtype.ext
  have hx : (x : G) ∈ (⊥ : Subgroup G) := hbot ▸ x.2
  have hy : (y : G) ∈ (⊥ : Subgroup G) := hbot ▸ y.2
  rw [Subgroup.mem_bot] at hx hy
  rw [hx, hy]

/-- The reduced identity-projection local strip has trivial geometric kernel:
its projection is the identity. -/
theorem localOFieldStrip_geometric_bot (v : PaperV) :
    DPrimeStrip.geometric localOFieldStrip.toDPrimeStrip v = ⊥ := by
  show (localOFieldStrip.toDPrimeStrip.proj v).ker = ⊥
  rw [show localOFieldStrip.toDPrimeStrip.proj v = MonoidHom.id _ from rfl]
  exact MonoidHom.ker_id

/-- The paper F-double-plus-prime-strip has nontrivial geometric kernel at
every place. -/
theorem fPsi_geometric_ne_bot (F : FPsiPrimeStrip l) (v : PaperV) :
    DPrimeStrip.geometric F.strip.toDPrimeStrip v ≠ ⊥ :=
  ne_bot_of_nontrivial (F.geometric_nontrivial v)

/-- The reduced strip is excluded.  No F-double-plus-prime-strip of the paper is
equivalent, as an F-prime-strip, to the identity-projection reduced strip
localOFieldStrip: strip equivalence would transfer triviality of the geometric
kernel, but the paper kernel is nontrivial. -/
theorem no_fPsi_equiv_localOFieldStrip (F : FPsiPrimeStrip l) (v : PaperV) :
    ¬ Nonempty (FPrimeStripEquiv F.strip localOFieldStrip) := by
  rintro ⟨phi⟩
  have hbot : ∀ w : PaperV,
      DPrimeStrip.geometric localOFieldStrip.toDPrimeStrip w = ⊥ :=
    fun w => localOFieldStrip_geometric_bot w
  exact fPsi_geometric_ne_bot F v
    (geometric_eq_bot_of_stripEquiv phi.symm.toD hbot v)

/-- The degenerate S1487 monoid is excluded from (a).  The local monoids of the
paper F-double-plus-prime-strip cannot be identified with the unit group of the
degenerate S1487 value monoid. -/
theorem fPsi_mon_not_sourceHaar (F : FPsiPrimeStrip l) (v : PaperV) :
    ¬ Nonempty (F.strip.Mon v ≃* SourceHaarActualValueMonoidˣ) := by
  rw [F.mon_eq v]
  exact @no_localOFieldUnits_equiv_sourceHaarUnits v.1 ⟨v.prime⟩

/-- The first link of the missing chain: the curve pi_1 datum at every place. -/
theorem fPsi_curvePiOne (F : FPsiPrimeStrip l) (v : PaperV) :
    Nonempty (CurvePiOneData v) :=
  ⟨F.piOne v⟩

/-! ## 3. Component (b): the paper-level theta and Gaussian monoid -/

/-- (b) The paper-level theta and Gaussian monoid assignment Psi_env, Psi_gau of
IUT II, Corollary 4.6, (iv), on the actual F-double-plus-prime-strip and the
fixed finite theta packet of the actual input.  The theta values are the
Gaussian special values of the actual packet, and the evaluation is the
Gaussian evaluation of Proposition 4.1, (iv). -/
structure ThetaMonoidActual (I : Theorem311Source.OriginalInput l PaperV)
    (F : FPsiPrimeStrip l) where
  env : PaperV → Type
  gau : PaperV → Type
  [commMonoidEnv : ∀ v, CommMonoid (env v)]
  [commMonoidGau : ∀ v, CommMonoid (gau v)]
  thetaValue : (v : PaperV) → SignedLabel l.value → env v
  qElement : (v : PaperV) → env v
  thetaValue_eq : ∀ v (j : SignedLabel l.value),
    thetaValue v j = qElement v ^ (gaussExponent j.1).toNat
  evaluation : (v : PaperV) → env v →* gau v
  evaluation_bijective : ∀ v, Function.Bijective (evaluation v)
  valueMap : (v : PaperV) → env v →* ℝ≥0
  value_theta : ∀ v (j : SignedLabel l.value),
    valueMap v (thetaValue v j) = Real.toNNReal ((I.theaterAt 0 0).thetaPacket.scale j)
  value_q : ∀ v,
    valueMap v (qElement v) = Real.toNNReal ((I.theaterAt 0 0).thetaPacket.q)

/-! ## 4. Component (c): the group-theoretic O-times-mu(G) actor -/

/-- (c) The group-theoretic actor O-times-mu(G) of IUT II, Example 1.8,
(iii)--(iv).  alg is the construction from a profinite group G alone, algMap
its functoriality under isomorphisms of profinite groups, and the actor at each
place is alg evaluated at the actual local absolute Galois group, identified
with the actual local O-times-mu. -/
structure OUnitsMuActor (l : PrimeGeFive) (F : FPsiPrimeStrip l) where
  alg : ProfiniteGrp → Type
  [commMonoidAlg : ∀ G : ProfiniteGrp, CommMonoid (alg G)]
  algMap : ∀ {G H : ProfiniteGrp}, G ≃* H → alg G ≃* alg H
  actor : PaperV → Type
  [commMonoidActor : ∀ v, CommMonoid (actor v)]
  actor_eq : ∀ v, actor v = alg (@localAbsoluteGaloisProfinite v.1 ⟨v.prime⟩)
  actor_equiv_local : ∀ v, Nonempty (actor v ≃* LocalOFieldUnitsMuAt v)
  action : ∀ v, @LocalAbsoluteGalois v.1 ⟨v.prime⟩ →* MulAut (actor v)

/-- The actual local O-times-mu is nontrivial (S1978), while the S1487 unit
group is a subsingleton, so the degenerate S1487 carrier cannot be the paper
actor. -/
theorem localUnitsMu_not_equiv_sourceHaarUnits (v : PaperV) :
    ¬ Nonempty (LocalOFieldUnitsMuAt v ≃* SourceHaarActualValueMonoidˣ) := by
  rintro ⟨e⟩
  haveI : Subsingleton (SourceHaarActualValueMonoidˣ) :=
    sourceHaarActualValueMonoid_units_subsingleton
  haveI : Subsingleton (LocalOFieldUnitsMuAt v) :=
    ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
  exact LocalOFieldUnitsMuAt_nontrivial v (Subsingleton.elim _ _)

/-- The actor cannot be carried by the degenerate S1487 O-times-mu. -/
theorem oUnitsMuActor_not_sourceHaar (F : FPsiPrimeStrip l) (A : OUnitsMuActor l F)
    (v : PaperV) :
    ¬ Nonempty (A.actor v ≃* SourceHaarActualValueMonoidˣ) := by
  rintro ⟨e⟩
  obtain ⟨f⟩ := A.actor_equiv_local v
  exact localUnitsMu_not_equiv_sourceHaarUnits v ⟨f.symm.trans e⟩

/-! ## 5. Component (e): the operation-level Kummer and evaluation -/

/-- (e) The operation-level Kummer isomorphism (IUT II, Definition 4.9, (i)) and
evaluation isomorphism (IUT II, Corollary 4.10, (ii)) between the
group-theoretic side O-times-mu(G_v) and the Frobenioid side O-times-mu of the
actual local monoid, together with the Gaussian evaluation on the theta
monoid. -/
structure OperationKummerEvaluation (I : Theorem311Source.OriginalInput l PaperV)
    (F : FPsiPrimeStrip l) (theta : ThetaMonoidActual I F)
    (A : OUnitsMuActor l F) (q : QPilotODaggerData l) where
  groupSide : PaperV → Type
  [commMonoidGroupSide : ∀ v, CommMonoid (groupSide v)]
  frobSide : PaperV → Type
  [commMonoidFrobSide : ∀ v, CommMonoid (frobSide v)]
  groupSide_eq : ∀ v, groupSide v = A.actor v
  frobSide_eq : ∀ v, frobSide v = LocalOFieldUnitsMuAt v
  kummer : ∀ v, groupSide v ≃* frobSide v
  evaluation : ∀ v, theta.env v ≃* theta.gau v
  evaluation_eq : ∀ v, (evaluation v).toMonoidHom = theta.evaluation v
  qPilot_evaluation : ∀ v,
    theta.valueMap v (theta.qElement v) =
      Real.toNNReal ((I.theaterAt 0 0).thetaPacket.q)

/-- The S1487 O-times-mu cannot be the Frobenioid side of the operation-level
Kummer isomorphism. -/
theorem operationKummer_frobSide_not_sourceHaar
    (E : OperationKummerEvaluation I F theta A q) (v : PaperV) :
    ¬ Nonempty (E.frobSide v ≃* SourceHaarActualValueMonoidˣ) := by
  rw [E.frobSide_eq v]
  exact localUnitsMu_not_equiv_sourceHaarUnits v

/-! ## 6. The paper O object and its exact first-missing chain -/

/-- The paper actual O object.  Its five components are exactly the components
of IUT II, Definitions 1.1 and 4.9, Example 1.8, and Corollary 4.10, (ii):
(a) the actual F-double-plus-prime-strip, (b) the paper-level theta/Gaussian
monoid, (c) the group-theoretic O-times-mu(G) actor, (d) the actual q-pilot
O-triangle generator, and (e) the operation-level Kummer/evaluation. -/
structure PaperOActual (I : Theorem311Source.OriginalInput l PaperV) where
  fStackPlus : FPsiPrimeStrip l
  theta : ThetaMonoidActual I fStackPlus
  oUnitsMu : OUnitsMuActor l fStackPlus
  qPilot_generator : (paperQPilotODaggerData l).generator = qPilotODaggerGenerator l
  qPilot_not_sourceHaar :
    ¬ Nonempty (qPilotODaggerCarrier l ≃* SourceHaarActualValueMonoid)
  kummer : OperationKummerEvaluation I fStackPlus theta oUnitsMu
    (paperQPilotODaggerData l)

/-- The exact first-missing bundle of the paper O object: components (a), (b),
(c), (e), with the constructed q-pilot (d) already fixed. -/
structure PaperOFirstMissing (I : Theorem311Source.OriginalInput l PaperV) where
  fStackPlus : FPsiPrimeStrip l
  theta : ThetaMonoidActual I fStackPlus
  oUnitsMu : OUnitsMuActor l fStackPlus
  kummer : OperationKummerEvaluation I fStackPlus theta oUnitsMu
    (paperQPilotODaggerData l)

/-- The first-missing bundle of a paper O object. -/
def paperOFirstMissing_of_actual (X : PaperOActual I) : PaperOFirstMissing I where
  fStackPlus := X.fStackPlus
  theta := X.theta
  oUnitsMu := X.oUnitsMu
  kummer := X.kummer

/-- A paper O object from its first-missing bundle and the constructed
q-pilot. -/
def paperOActual_of_firstMissing (M : PaperOFirstMissing I) : PaperOActual I where
  fStackPlus := M.fStackPlus
  theta := M.theta
  oUnitsMu := M.oUnitsMu
  qPilot_generator := rfl
  qPilot_not_sourceHaar := qPilotODaggerCarrier_no_equiv_sourceHaar l
  kummer := M.kummer

/-- The paper O object is nonempty exactly when its first-missing bundle is.
The q-pilot component (d) is constructed outright; the remaining four
components are the exact first missing. -/
theorem nonempty_paperOActual_iff (I : Theorem311Source.OriginalInput l PaperV) :
    Nonempty (PaperOActual I) ↔ Nonempty (PaperOFirstMissing I) := by
  constructor
  · rintro ⟨X⟩
    exact ⟨paperOFirstMissing_of_actual X⟩
  · rintro ⟨M⟩
    exact ⟨paperOActual_of_firstMissing M⟩

/-- The first link of the missing chain, restated for the first-missing bundle:
an actual curve pi_1 datum at every place. -/
theorem firstMissing_curvePiOne (M : PaperOFirstMissing I) (v : PaperV) :
    Nonempty (CurvePiOneData v) :=
  fPsi_curvePiOne M.fStackPlus v

/-- The first missing bundle excludes the reduced identity-projection strip. -/
theorem firstMissing_excludes_reduced (M : PaperOFirstMissing I) (v : PaperV) :
    ¬ Nonempty (FPrimeStripEquiv M.fStackPlus.strip localOFieldStrip) :=
  no_fPsi_equiv_localOFieldStrip M.fStackPlus v

/-- The paper O object has the actual local O-times monoids, not the degenerate
S1487 monoid. -/
theorem paperOActual_mon_not_sourceHaar (X : PaperOActual I) (v : PaperV) :
    ¬ Nonempty (X.fStackPlus.strip.Mon v ≃* SourceHaarActualValueMonoidˣ) :=
  fPsi_mon_not_sourceHaar X.fStackPlus v

/-- The paper O object q-pilot generator is the actual q = l and its carrier is
not the degenerate S1487 value monoid. -/
theorem paperOActual_qPilot_actual (X : PaperOActual I) :
    ((paperQPilotODaggerData l).generator : ℚ_[l.value]) = qPilotValue l ∧
      ¬ Nonempty (qPilotODaggerCarrier l ≃* SourceHaarActualValueMonoid) :=
  ⟨rfl, X.qPilot_not_sourceHaar⟩

/-! ## 7. Axiom probes -/

#print axioms qPilotODaggerCarrier_no_equiv_sourceHaar
#print axioms qPilotValue_pow_injective
#print axioms paperQPilotODaggerData
#print axioms no_fPsi_equiv_localOFieldStrip
#print axioms fPsi_mon_not_sourceHaar
#print axioms localUnitsMu_not_equiv_sourceHaarUnits
#print axioms nonempty_paperOActual_iff
#print axioms paperOActual_qPilot_actual

end LeanFormal.IUT.XiFPaper.S2038PaperOActual
