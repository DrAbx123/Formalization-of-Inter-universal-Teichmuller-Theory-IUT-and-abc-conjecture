import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData

/-!
  # A concrete nonpositive value model for `SourceUnitRegionHaarData`

  The interface `SourceUnitRegionHaarData` is parameterized by a source input `I`
  and a value realization `R`.  The general value-monoid carrier can have
  unbounded log-degree, so the interface is not automatic.  This file constructs
  a concrete, nonempty carrier on which it is automatic: the value monoid is the
  additive monoid of nonpositive reals, the degree map is the inclusion into the
  multiplicative reals, and the source realization is the unique homomorphism
  from the positive reals to this monoid.  The theta packet has `q = 1`, so the
  `degree_of_q` field is exactly the zero equality.

  The source family is concrete and infinite: at index `(n,m)` the prime-strip
  projection is the shear matrix `[[1+n*m,n],[m,1]]` on `Z^2`; these matrices are
  pairwise conjugate by an automorphism, while their entries recover `(n,m)`.
  The unit region used for the Haar datum is the actual source holomorphic hull,
  not `Set.univ`, and `scaling = 1`, `degreeBound = 0`.

  This is a value-layer model, not the paper's ring-of-integers carrier: all
  value points have nonpositive log-degree by construction, and the source theta
  packet is the constant `q = 1` packet.  It does not claim that the paper's
  `1, circ U` region has been constructed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua

open scoped BigOperators
open Theorem311Source
open OriginalInput

/-! ## 1. The nonpositive value monoid -/

/-- The additive monoid of nonpositive real numbers. -/
def sourceHaarActualNonpositiveAddSubmonoid : AddSubmonoid Real where
  carrier := {x : Real | x ≤ 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simpa using add_nonpos hx hy

/-- The value monoid of the concrete model: nonpositive reals under addition. -/
abbrev SourceHaarActualValueMonoid : Type :=
  Multiplicative sourceHaarActualNonpositiveAddSubmonoid

/-- The degree map of the model.  It is the inclusion of the nonpositive reals
  into the multiplicative reals; every value has nonpositive degree. -/
def sourceHaarActualDegree : SourceHaarActualValueMonoid →* Multiplicative Real where
  toFun x := Multiplicative.ofAdd
    ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real)
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The concrete degree is nonpositive on every value point. -/
theorem sourceHaarActualDegree_nonpos (x : SourceHaarActualValueMonoid) :
    Multiplicative.toAdd (sourceHaarActualDegree x) ≤ 0 := by
  change ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real) ≤ 0
  have hx := (Multiplicative.toAdd x).property
  change ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real) ≤ 0 at hx
  exact hx

/-- The unique monoid homomorphism from the positive reals to the nonpositive
  value monoid.  Its image is the identity value, because a group can map to a
  monoid of nonpositive degrees only trivially. -/
def sourceHaarActualPositiveRealAction :
    Multiplicative Real →* SourceHaarActualValueMonoid where
  toFun _ := 1
  map_one' := rfl
  map_mul' := by
    intro x y
    simp

/-! ## 2. The concrete prime strips and source family -/

/-- The trivial action of a group on the nonpositive value monoid. -/
def sourceHaarActualTrivialAction (P M : Type) [Group P] [CommMonoid M] :
    P →* MulAut M where
  toFun _ := 1
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The shear matrix `[[1+n*m,n],[m,1]]` as an additive equivalence of `Z^2`.
  Its inverse is `[[1,-n],[-m,1+n*m]]`. -/
def sourceHaarActualShearAddEquiv (n m : Int) : (Int × Int) ≃+ (Int × Int) where
  toFun x := ((1 + n * m) * x.1 + n * x.2, m * x.1 + x.2)
  invFun x := (x.1 - n * x.2, -m * x.1 + (1 + n * m) * x.2)
  left_inv := by
    intro x
    ext <;> dsimp <;> ring
  right_inv := by
    intro x
    ext <;> dsimp <;> ring
  map_add' := by
    intro x y
    ext <;> dsimp <;> ring

/-- The multiplicative version of the shear equivalence. -/
def sourceHaarActualShearMulEquiv (n m : Int) :
    Multiplicative (Int × Int) ≃* Multiplicative (Int × Int) :=
  (sourceHaarActualShearAddEquiv n m).toMultiplicative

/-- The canonical group structure used on the integer-pair group in the model. -/
def sourceHaarActualIntPairGroup : Group (Multiplicative (Int × Int)) :=
  inferInstance

/-- The concrete prime strip at index `(n,m)`: the projection is the shear
  automorphism of `Z^2`, the value monoid is nonpositive, and the action and
  degree are the model maps. -/
def sourceHaarActualPrimeStrip (n m : Int) : FPrimeStrip.{0, 0, 0} Unit where
  Pi := fun _ => Multiplicative (Int × Int)
  groupPi := fun _ => sourceHaarActualIntPairGroup
  G := fun _ => Multiplicative (Int × Int)
  groupG := fun _ => sourceHaarActualIntPairGroup
  proj := fun _ =>
    (sourceHaarActualShearMulEquiv n m :
      Multiplicative (Int × Int) →* Multiplicative (Int × Int))
  proj_surjective := fun _ => (sourceHaarActualShearMulEquiv n m).surjective
  Mon := fun _ => SourceHaarActualValueMonoid
  commMonoidMon := fun _ => inferInstance
  action := fun _ =>
    sourceHaarActualTrivialAction (Multiplicative (Int × Int))
      SourceHaarActualValueMonoid
  degree := fun _ => sourceHaarActualDegree

/-- The constant theta packet with `q = 1`. -/
def sourceHaarActualThetaPacket (l : PrimeGeFive) : FiniteThetaPacket l :=
  FiniteThetaPacket.ofQ (l := l) 1 (by norm_num)

/-- The concrete Hodge theater at index `(n,m)` over a fixed arithmetic input. -/
def sourceHaarActualTheater (A : InitialThetaArithmeticData.{ua} l)
    (i : SourceTheorem311Index) : HodgeTheater.{ua, 0, 0, 0} l Unit where
  arithmetic := A
  primeStrip := sourceHaarActualPrimeStrip i.1 i.2
  thetaPacket := sourceHaarActualThetaPacket l

/-- The canonical equivalence between two concrete prime strips: the identity on
  the projective group and the shear conjugator on the value group. -/
def sourceHaarActualPrimeStripEquiv (i j : SourceTheorem311Index) :
    FPrimeStripEquiv (sourceHaarActualPrimeStrip i.1 i.2)
      (sourceHaarActualPrimeStrip j.1 j.2) where
  isoPi := fun _ => MulEquiv.refl _
  isoG := fun _ =>
    (sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
      (sourceHaarActualShearMulEquiv j.1 j.2)
  isoMon := fun _ => MulEquiv.refl _
  compatProj := by
    intro v
    ext x
    change sourceHaarActualShearMulEquiv j.1 j.2 x =
      ((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
        (sourceHaarActualShearMulEquiv j.1 j.2))
        (sourceHaarActualShearMulEquiv i.1 i.2 x)
    simp [MulEquiv.trans_apply]
  compatAction := by
    intro v g x
    rfl
  compatDegree := by
    intro v x
    rfl

/-- Componentwise extensionality for the concrete prime-strip equivalences. -/
theorem sourceHaarActualFPrimeStripEquiv_ext
    {F F' : FPrimeStrip.{0, 0, 0} Unit}
    {phi psi : FPrimeStripEquiv F F'}
    (hPi : ∀ v, phi.isoPi v = psi.isoPi v)
    (hG : ∀ v, phi.isoG v = psi.isoG v)
    (hMon : ∀ v, phi.isoMon v = psi.isoMon v) : phi = psi := by
  cases phi
  cases psi
  simp only at hPi hG hMon
  congr
  all_goals first
    | exact funext hPi
    | exact funext hG
    | exact funext hMon

/-- Componentwise extensionality for the concrete theater links. -/
theorem sourceHaarActualHodgeTheaterLink_ext
    {L M : HodgeTheaterLink (sourceHaarActualTheater (l := l) A i)
      (sourceHaarActualTheater (l := l) A j)}
    (h : L.primeStripEquiv = M.primeStripEquiv) : L = M := by
  cases L
  cases M
  simp only at h
  congr

/-- The self-equivalence of a concrete prime strip is the identity. -/
theorem sourceHaarActualPrimeStripEquiv_self (i : SourceTheorem311Index) :
    sourceHaarActualPrimeStripEquiv i i =
      FPrimeStripEquiv.refl (sourceHaarActualPrimeStrip i.1 i.2) := by
  refine sourceHaarActualFPrimeStripEquiv_ext ?_ ?_ ?_
  · intro v
    rfl
  · intro v
    exact MulEquiv.symm_trans_self _
  · intro v
    rfl

/-- The canonical link between two concrete theaters. -/
def sourceHaarActualTheaterLink (A : InitialThetaArithmeticData.{ua} l)
    (i j : SourceTheorem311Index) :
    HodgeTheaterLink (sourceHaarActualTheater (l := l) A i)
      (sourceHaarActualTheater (l := l) A j) where
  primeStripEquiv := sourceHaarActualPrimeStripEquiv i j
  theta_q_eq := rfl
  theta_scale_eq := by
    intro j
    rfl

/-- The canonical link is reflexive. -/
theorem sourceHaarActualTheaterLink_refl
    (A : InitialThetaArithmeticData.{ua} l) (i : SourceTheorem311Index) :
    sourceHaarActualTheaterLink (l := l) A i i =
      HodgeTheaterLink.refl (sourceHaarActualTheater (l := l) A i) := by
  refine sourceHaarActualHodgeTheaterLink_ext ?_
  exact sourceHaarActualPrimeStripEquiv_self i

/-- The canonical prime-strip equivalence is compatible with symmetry. -/
theorem sourceHaarActualPrimeStripEquiv_symm (i j : SourceTheorem311Index) :
    FPrimeStripEquiv.symm (sourceHaarActualPrimeStripEquiv i j) =
      sourceHaarActualPrimeStripEquiv j i := by
  refine sourceHaarActualFPrimeStripEquiv_ext ?_ ?_ ?_
  · intro v
    rfl
  · intro v
    ext x
    change ((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
        (sourceHaarActualShearMulEquiv j.1 j.2)).symm x =
      ((sourceHaarActualShearMulEquiv j.1 j.2).symm.trans
        (sourceHaarActualShearMulEquiv i.1 i.2)) x
    rw [MulEquiv.symm_trans_apply, MulEquiv.trans_apply]
    rfl
  · intro v
    rfl

/-- The canonical link is compatible with symmetry. -/
theorem sourceHaarActualTheaterLink_symm
    (A : InitialThetaArithmeticData.{ua} l) (i j : SourceTheorem311Index) :
    HodgeTheaterLink.symm (sourceHaarActualTheaterLink (l := l) A i j) =
      sourceHaarActualTheaterLink (l := l) A j i := by
  refine sourceHaarActualHodgeTheaterLink_ext ?_
  exact sourceHaarActualPrimeStripEquiv_symm i j

/-- The canonical prime-strip equivalences compose. -/
theorem sourceHaarActualPrimeStripEquiv_trans (i j k : SourceTheorem311Index) :
    FPrimeStripEquiv.trans (sourceHaarActualPrimeStripEquiv i j)
        (sourceHaarActualPrimeStripEquiv j k) =
      sourceHaarActualPrimeStripEquiv i k := by
  refine sourceHaarActualFPrimeStripEquiv_ext ?_ ?_ ?_
  · intro v
    rfl
  · intro v
    ext x
    change ((sourceHaarActualShearMulEquiv j.1 j.2).symm.trans
        (sourceHaarActualShearMulEquiv k.1 k.2))
        (((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
          (sourceHaarActualShearMulEquiv j.1 j.2)) x) =
      ((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
        (sourceHaarActualShearMulEquiv k.1 k.2)) x
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  · intro v
    rfl

/-- The canonical links compose. -/
theorem sourceHaarActualTheaterLink_trans
    (A : InitialThetaArithmeticData.{ua} l) (i j k : SourceTheorem311Index) :
    HodgeTheaterLink.trans (sourceHaarActualTheaterLink (l := l) A i j)
        (sourceHaarActualTheaterLink (l := l) A j k) =
      sourceHaarActualTheaterLink (l := l) A i k := by
  refine sourceHaarActualHodgeTheaterLink_ext ?_
  exact sourceHaarActualPrimeStripEquiv_trans i j k

/-- The concrete theaters at distinct indices are distinct.  The projection of
  the shear matrix at `(0,1)` recovers `n`, and at `(1,0)` recovers `m`. -/
theorem sourceHaarActualTheater_injective
    (A : InitialThetaArithmeticData.{ua} l) :
    Function.Injective (sourceHaarActualTheater (l := l) A) := by
  intro i j h
  have hstrip : (sourceHaarActualTheater (l := l) A i).primeStrip =
      (sourceHaarActualTheater (l := l) A j).primeStrip :=
    congrArg HodgeTheater.primeStrip h
  have hprojHEq : HEq ((sourceHaarActualTheater (l := l) A i).primeStrip.proj ())
      ((sourceHaarActualTheater (l := l) A j).primeStrip.proj ()) :=
    congr_arg_heq (fun T : HodgeTheater.{ua, 0, 0, 0} l Unit =>
      T.primeStrip.proj ()) h
  have hprojHEq' : HEq ((sourceHaarActualPrimeStrip i.1 i.2).proj ())
      ((sourceHaarActualPrimeStrip j.1 j.2).proj ()) := hprojHEq
  have hproj : (sourceHaarActualPrimeStrip i.1 i.2).proj () =
      (sourceHaarActualPrimeStrip j.1 j.2).proj () := eq_of_heq hprojHEq'
  have h01 := DFunLike.congr_fun hproj (Multiplicative.ofAdd ((0 : Int), (1 : Int)))
  have h10 := DFunLike.congr_fun hproj (Multiplicative.ofAdd ((1 : Int), (0 : Int)))
  have hn : i.1 = j.1 := by
    have h01' : Multiplicative.ofAdd
        (sourceHaarActualShearAddEquiv i.1 i.2 ((0 : Int), (1 : Int))) =
        Multiplicative.ofAdd
          (sourceHaarActualShearAddEquiv j.1 j.2 ((0 : Int), (1 : Int))) := h01
    have h := congrArg (fun x => (Multiplicative.toAdd x).1) h01'
    simpa [sourceHaarActualShearAddEquiv] using h
  have hm : i.2 = j.2 := by
    have h10' : Multiplicative.ofAdd
        (sourceHaarActualShearAddEquiv i.1 i.2 ((1 : Int), (0 : Int))) =
        Multiplicative.ofAdd
          (sourceHaarActualShearAddEquiv j.1 j.2 ((1 : Int), (0 : Int))) := h10
    have h := congrArg (fun x => (Multiplicative.toAdd x).2) h10'
    simpa [sourceHaarActualShearAddEquiv] using h
  exact Prod.ext hn hm

/-- The concrete infinite source family over a fixed arithmetic input. -/
def sourceHaarActualFamily (A : InitialThetaArithmeticData.{ua} l) :
    SourceHodgeTheaterFamily.{ua, 0, 0, 0, 0} l Unit where
  index := SourceTheorem311Index
  theater := sourceHaarActualTheater (l := l) A
  distinct := sourceHaarActualTheater_injective (l := l) A
  link := sourceHaarActualTheaterLink (l := l) A
  link_refl := sourceHaarActualTheaterLink_refl (l := l) A
  link_symm := sourceHaarActualTheaterLink_symm (l := l) A
  link_trans := sourceHaarActualTheaterLink_trans (l := l) A
  permutation := Equiv.refl SourceTheorem311Index
  permutationLink := fun i =>
    HodgeTheaterLink.refl (sourceHaarActualTheater (l := l) A i)
  permutation_naturality := by
    intro i j
    change HodgeTheaterLink.trans (sourceHaarActualTheaterLink (l := l) A i j)
        (HodgeTheaterLink.refl (sourceHaarActualTheater (l := l) A j)) =
      HodgeTheaterLink.trans
        (HodgeTheaterLink.refl (sourceHaarActualTheater (l := l) A i))
        (sourceHaarActualTheaterLink (l := l) A i j)
    rw [HodgeTheaterLink.trans_refl, HodgeTheaterLink.refl_trans]

/-- A concrete `OriginalInput` over any supplied source datum `S`: all theaters
  use the arithmetic input of `S`, and the family index is identified with
  `Int × Int` by the identity equivalence. -/
def sourceHaarActualOriginalInput (S : SourceDefinition31Data.{ua} l) :
    OriginalInput.{ua, 0, 0, 0, 0} l Unit where
  initial := S
  family := sourceHaarActualFamily (l := l) S.arithmetic
  index_equiv := Equiv.refl SourceTheorem311Index
  arithmetic_alignment := by
    intro i
    rfl

/-- The prime strip selected by the concrete original input is the concrete
  prime strip at the same integer index. -/
theorem sourceHaarActual_primeStripAt
    (S : SourceDefinition31Data.{ua} l) (n m : Int) :
    (sourceHaarActualOriginalInput (l := l) S).primeStripAt n m =
      sourceHaarActualPrimeStrip n m :=
  rfl

/-- The `q`-parameter of the concrete original input is `1` at every index. -/
theorem sourceHaarActual_originalInput_theta_q
    (S : SourceDefinition31Data.{ua} l) (n m : Int) :
    ((sourceHaarActualOriginalInput (l := l) S).theaterAt n m).thetaPacket.q = 1 :=
  rfl

/-! ## 3. The concrete realization and its Haar datum -/

/-- The concrete source realization: positive reals map to the identity of the
  nonpositive value monoid.  Since the theta packet has `q = 1`, the
  `degree_of_q` faithfulness field is the zero equality. -/
def sourceHaarActualImageRealization (S : SourceDefinition31Data.{ua} l) :
    (sourceHaarActualOriginalInput (l := l) S).SourceImageRealization () where
  posRealAction := sourceHaarActualPositiveRealAction
  degree_of_q := by
    rw [sourceHaarActual_originalInput_theta_q (l := l) S 0 0, Real.log_one]
    change (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 ()
      (1 : SourceHaarActualValueMonoid) = 0
    exact (sourceHaarActualOriginalInput (l := l) S).logDegreeAt_one 0 0 ()

/-- The concrete log-degree at every index is the underlying nonpositive real. -/
theorem sourceHaarActual_logDegreeAt_eq (S : SourceDefinition31Data.{ua} l)
    (n m : Int) (x : SourceHaarActualValueMonoid) :
    (sourceHaarActualOriginalInput (l := l) S).logDegreeAt n m () x =
      ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real) := by
  change Multiplicative.toAdd
    ((sourceHaarActualPrimeStrip n m).degree () x) =
      ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real)
  rfl

/-- Every global value point of the concrete model has nonpositive log-degree. -/
theorem sourceHaarActual_sourceLocalLogDegree_nonpos
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l)
    (x : (sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ()) :
    (sourceHaarActualOriginalInput (l := l) S).sourceLocalLogDegree () x ≤ 0 := by
  unfold OriginalInput.sourceLocalLogDegree
  refine Finset.sum_nonpos ?_
  intro i _
  rw [sourceHaarActual_logDegreeAt_eq]
  have hx := (Multiplicative.toAdd (x i)).property
  change ((Multiplicative.toAdd (x i) : sourceHaarActualNonpositiveAddSubmonoid) : Real) ≤ 0 at hx
  exact hx

/-- The actual unit region of the model: the source holomorphic hull itself. -/
def sourceHaarActualUnitRegion (S : SourceDefinition31Data.{ua} l)
    (n : ThetaPilotCarrier l) :
    Set ((sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ()) :=
  ((sourceHaarActualOriginalInput (l := l) S).sourceHolomorphicHull
    () (sourceHaarActualImageRealization (l := l) S) n : Set _)

/-- The concrete `SourceUnitRegionHaarData`: unit region the actual hull,
  scaling `1`, bound `0`, and both degree bounds supplied by the nonpositive
  value monoid. -/
def sourceHaarActualData (S : SourceDefinition31Data.{ua} l)
    (n : ThetaPilotCarrier l) :
    (sourceHaarActualOriginalInput (l := l) S).SourceUnitRegionHaarData ()
      (sourceHaarActualImageRealization (l := l) S) n where
  unitRegion := sourceHaarActualUnitRegion (l := l) S n
  scaling := 1
  degreeBound := 0
  hull_subset_scaledRegionImage := by
    intro x hx
    exact ⟨x, hx, (one_mul x).symm⟩
  unitRegion_logDegree_le := by
    intro y _
    exact sourceHaarActual_sourceLocalLogDegree_nonpos (l := l) S n y
  scaling_logDegree_nonpos := by
    rw [(sourceHaarActualOriginalInput (l := l) S).sourceLocalLogDegree_one ()]

/-- The unit region of the model is definitionally the actual source hull. -/
theorem sourceHaarActualData_unitRegion (S : SourceDefinition31Data.{ua} l)
    (n : ThetaPilotCarrier l) :
    (sourceHaarActualData (l := l) S n).unitRegion =
      ((sourceHaarActualOriginalInput (l := l) S).sourceHolomorphicHull
        () (sourceHaarActualImageRealization (l := l) S) n : Set _) :=
  rfl

/-- The scaling of the model is the monoid unit, with zero log-degree. -/
theorem sourceHaarActualData_scaling (S : SourceDefinition31Data.{ua} l)
    (n : ThetaPilotCarrier l) :
    (sourceHaarActualData (l := l) S n).scaling = 1 :=
  rfl

/-- The hull is nonempty: it contains the monoid unit. -/
theorem sourceHaarActualData_unitRegion_nonempty
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    (sourceHaarActualData (l := l) S n).unitRegion.Nonempty := by
  refine ⟨1, ?_⟩
  rw [sourceHaarActualData_unitRegion]
  refine subset_holomorphicHull ?_
  refine ⟨zeroSignedLabel, ?_⟩
  ext p
  rfl

/-- A concrete point of the model with every component `-1`. -/
def sourceHaarActualMinusOne : sourceHaarActualNonpositiveAddSubmonoid :=
  ⟨(-1 : Real), by simp [sourceHaarActualNonpositiveAddSubmonoid]⟩

/-- A concrete point of the model with every component `-1`. -/
def sourceHaarActualStrictPoint (S : SourceDefinition31Data.{ua} l) :
    (sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint () :=
  fun _ => Multiplicative.ofAdd sourceHaarActualMinusOne

/-- The strict point has log-degree `-|SourceVolumeIndex|`, in particular a
  strictly negative value.  This records that the model's value carrier is not a
  subsingleton. -/
theorem sourceHaarActualStrictPoint_logDegree
    (S : SourceDefinition31Data.{ua} l) :
    (sourceHaarActualOriginalInput (l := l) S).sourceLocalLogDegree ()
        (sourceHaarActualStrictPoint (l := l) S) =
      - (Fintype.card (SourceVolumeIndex l) : Real) := by
  unfold OriginalInput.sourceLocalLogDegree
  have h : ∀ i : SourceVolumeIndex l,
      (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 ()
        ((sourceHaarActualStrictPoint (l := l) S) i) = -1 := by
    intro i
    rw [sourceHaarActual_logDegreeAt_eq]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ]
  simp [nsmul_eq_mul]

/-- The strict point lies in the unit region, so the actual hull is not the
  singleton `{1}`. -/
theorem sourceHaarActualStrictPoint_mem_unitRegion
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    sourceHaarActualStrictPoint (l := l) S ∈
      (sourceHaarActualData (l := l) S n).unitRegion := by
  rw [sourceHaarActualData_unitRegion]
  change sourceHaarActualStrictPoint (l := l) S ∈
    (sourceHaarActualOriginalInput (l := l) S).sourceHolomorphicHull
      () (sourceHaarActualImageRealization (l := l) S) n
  rw [OriginalInput.sourceHolomorphicHull, mem_holomorphicHull_iff]
  intro H hH hS
  have h1S : (1 : (sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ()) ∈
      (sourceHaarActualOriginalInput (l := l) S).possibleThetaPilotImageSet
        () (sourceHaarActualImageRealization (l := l) S) n := by
    refine ⟨zeroSignedLabel, ?_⟩
    ext p
    rfl
  have h1H : (1 : (sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ()) ∈ H :=
    hS h1S
  have hstrict : sourceHaarActualStrictPoint (l := l) S ∈
      (sourceHaarActualOriginalInput (l := l) S).sourceScalingUnits () := by
    intro p h
    have hEq : sourceHaarActualMinusOne = 0 := by
      have hto := congrArg Multiplicative.toAdd h
      change (sourceHaarActualMinusOne : sourceHaarActualNonpositiveAddSubmonoid) = 0 at hto
      exact hto
    have hreal : (-1 : Real) = 0 :=
      congrArg (fun q : sourceHaarActualNonpositiveAddSubmonoid => (q : Real)) hEq
    norm_num at hreal
  simpa using hH (sourceHaarActualStrictPoint (l := l) S) hstrict 1 h1H

end

end LeanFormal.IUT
