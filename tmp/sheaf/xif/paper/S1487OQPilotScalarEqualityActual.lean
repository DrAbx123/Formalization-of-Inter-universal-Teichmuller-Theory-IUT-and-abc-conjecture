import tmp.sheaf.xif.paper.OrigXiFPaperQPilotScalarActual
import tmp.sheaf.xif.paper.OrigXiFThetaLinkActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket

/-!
# S1487: the O-layer q-pilot scalar equality on the concrete Gaussian C3

Layer: **O** (原文 Θ-link xi-f / 原文 q-pilot object).  The file works only on
the O-layer objects of S1391 / S1438 / S1463 and the concrete Gaussian
arithmetic input; it does not touch the normalized model (N), the native
target (T), the D4-D9 assembly (D), or the SourceDefinition31Data contract
beyond the explicit source data constructed below.  Name prefix: `S1487`.

## The target

S1463 (`OrigXiFThetaLinkActual`) carries the first exact scalar field

  scalar_eq : O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3

with `O.qPilotLogVolume = sourceQPilotSignedLog I.initial` by the object's own
`qPilotLogVolume_eq`, and S1391's actual L-carrier C3 giving

  OrigXiFPaperQPilotLogVolume C3 = -|Real.log ||C3.q.q|||.

Hence the O-layer scalar field is, definitionally, the equality

  sourceQPilotSignedLog I.initial = -|Real.log ||C3.q.q|||,

i.e. the **bad-place family sum** `- sum_b |log q_b|` against the **single
completion q** of the actual Gaussian L-carrier.  `OrigXiFPaperQPilotScalarActual`
already proves this exact reduction (see `_iff_neg_abs`, `_iff_sum`); §1
restates it in the form used here and adds the arithmetic evaluation of the
single-completion side.

## What is proved here (both answers, no assumption of the target)

1. **Arithmetic evaluation of the single completion q.**  For the concrete
   Gaussian place above 5, the actual completion norm is evaluated with
   Mathlib's arithmetic norm (`ArithmeticQPilotBaseChange`):

     ||C3.q.q|| = residueNormBase(place) ^ (-exponent),
     -|log ||C3.q.q||| = - (order * log 5),

   with `order >= 1` and `residueNormBase = 5` proved from the actual residue
   field `ZMod 5` of the chosen place (S1280/Example36 file).  In particular
   the single-q side is strictly negative and at most `-log 5`.

2. **A faithful one-place source datum: the equality is TRUE.**  Taking the
   Definition 3.1(b) bad family to be a one-element family whose q-parameter is
   the *actual* completion q magnitude `||q||`, the bad-family sum is exactly
   the single completion q magnitude, and the O-layer scalar field holds:
   `S1487FaithfulScalarEq` and, for any `O`,
   `OrigXiFThetaLinkActualScalarExactField O C3 = True`-proved.

3. **A two-place source datum: the equality is FALSE (actual counterexample).**
   Taking the same concrete Gaussian arithmetic and C3 but a *two-element* bad
   family with the same actual q parameters, the bad-family sum double-counts
   the actual magnitude:

     sourceQPilotSignedLog = -2 * localLogMagnitude q,   RHS = -localLogMagnitude q,

   which differ because the actual local magnitude is positive.  Therefore
   `OrigXiFPaperQPilotScalarExactFirstField` is false, and in particular the
   O-layer `scalar_eq` field of S1463 is false for **every** paper q-pilot
   object `O` over this concrete input and C3: no `OrigXiFThetaLinkActual`
   inhabitant exists at that data.  A third variant with the explicitly
   rational q-parameters `1/2` gives the same refutation with the numbers
   `-log 4` against at most `-log 5`, independent of the value of the
   completion order.

## Status of the two source data

Both are literal inhabitants of `SourceDefinition31Data.{0} l` over the
concrete Gaussian arithmetic: the arithmetic, selected places, bad places and
the Definition 3.1(b)(c) reduction clause are concrete (actual completion q
magnitudes, real stable/multiplicative reduction predicates).  The remaining
Definition 3.1 clauses (torsion, orbicurve, sections, cusp) are filled with
explicit carriers only so that the source contract is inhabited; their content
is irrelevant to the scalar and is **not** claimed to be the paper's D5-D9
data.  The scalar conclusions mention only the bad-place clause and the actual
completion q, so this is a legitimate model of the source contract, not an
assumption of the target and not a replacement of the target by `True`.

No `sorry`, `admit`, `axiom`, `True`-slot for the target proposition,
arbitrary inhabitant, or circular use of the scalar field is present.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.SourceProcessionBoundary

universe u uG uL uC

variable {l : PrimeGeFive}

local instance s1487GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1487FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The concrete Gaussian C3 side: arithmetic evaluation -/

/-- The concrete finite place of the Gaussian field above 5, as a
`FinitePlaceAtPrime` of residue characteristic 5. -/
def S1487FivePlace : FinitePlaceAtPrime GaussianField 5 :=
  ⟨concreteGaussianFivePlace, concretePlace_rationalPrime_eq_five⟩

/-- The actual q-candidate at that place (the same classical uniformizer used
by `concreteQCandidate`). -/
noncomputable def S1487Cand : FinitePlaceQCandidate S1487FivePlace.val :=
  Classical.choice (finitePlaceQCandidate_nonempty S1487FivePlace.val)

/-- The arithmetic residue norm at the concrete Gaussian five place is 5. -/
theorem S1487_residueNormBase_five :
    residueNormBase S1487FivePlace.val = 5 := by
  show residueNormBase concreteGaussianFivePlace = 5
  unfold residueNormBase
  have hcard : Nat.card (NumberFieldFinitePlace.ResidueField concreteGaussianFivePlace) = 5 :=
    concreteGaussianFivePlaceResidueField_card
  have habs : Ideal.absNorm (concreteGaussianFivePlace.maximalIdeal.asIdeal) = 5 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simpa [NumberFieldFinitePlace.ResidueField, NumberFieldFinitePlace.underlyingPrime]
      using hcard
  rw [habs]
  norm_num

/-- The actual completion log magnitude at the concrete Gaussian five place is
`order * log 5`. -/
theorem S1487Cand_magnitude :
    localLogMagnitude S1487Cand = (S1487Cand.order : ℝ) * Real.log 5 := by
  rw [localLogMagnitude_eq_order_mul_log, S1487_residueNormBase_five]

/-- The actual completion log magnitude is positive. -/
theorem S1487Cand_magnitude_pos : 0 < localLogMagnitude S1487Cand :=
  localLogMagnitude_pos S1487Cand

/-- The actual completion log magnitude is `>= log 5`. -/
theorem S1487Cand_magnitude_ge_log_five :
    Real.log 5 ≤ localLogMagnitude S1487Cand := by
  rw [S1487Cand_magnitude]
  have hpos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have horder : (1 : ℝ) ≤ (S1487Cand.order : ℝ) := by
    exact_mod_cast S1487Cand.order_pos
  nlinarith [hpos, horder]

/-! ## 2. The concrete shear family of Hodge theaters (index `Int x Int`)

The S1463 scalar field is stated for a concrete `OriginalInput l
(FinitePrimePlace 2 7)`; the tree does not construct one, so it is constructed
here from the explicit shear model of `SourceHodgeTheaterFamily` already used
by `SourceUnitRegionHaarDataActual`, specialised to the concrete finite-prime
index type.  The arithmetic input is the concrete Gaussian one. -/

abbrev S1487W : Type := FinitePrimePlace 2 7

/-- A concrete base place index for reading the shear matrix. -/
def S1487w0 : S1487W :=
  ⟨2, by
    show 2 ∈ primeStrip 2 7
    exact ⟨le_rfl, by norm_num, Nat.prime_two⟩⟩

/-- The shear strip over the concrete finite-prime index type. -/
noncomputable def S1487Strip (n m : Int) : FPrimeStrip.{0, 0, 0} S1487W where
  Pi := fun _ => Multiplicative (Int × Int)
  groupPi := fun _ => inferInstance
  G := fun _ => Multiplicative (Int × Int)
  groupG := fun _ => inferInstance
  proj := fun _ => (sourceHaarActualShearMulEquiv n m :
    Multiplicative (Int × Int) →* Multiplicative (Int × Int))
  proj_surjective := fun _ => (sourceHaarActualShearMulEquiv n m).surjective
  Mon := fun _ => SourceHaarActualValueMonoid
  commMonoidMon := fun _ => inferInstance
  action := fun _ =>
    sourceHaarActualTrivialAction (Multiplicative (Int × Int))
      SourceHaarActualValueMonoid
  degree := fun _ => sourceHaarActualDegree

/-- The canonical equivalence between two shear strips. -/
noncomputable def S1487StripEquiv (i j : SourceTheorem311Index) :
    FPrimeStripEquiv (S1487Strip i.1 i.2) (S1487Strip j.1 j.2) where
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

/-- Componentwise extensionality for the shear-strip equivalences. -/
theorem S1487StripEquiv_ext
    {F F' : FPrimeStrip.{0, 0, 0} S1487W}
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

/-- The self-equivalence of a shear strip is the identity. -/
theorem S1487StripEquiv_self (i : SourceTheorem311Index) :
    S1487StripEquiv i i = FPrimeStripEquiv.refl (S1487Strip i.1 i.2) := by
  refine S1487StripEquiv_ext ?_ ?_ ?_
  · intro v; rfl
  · intro v; exact MulEquiv.symm_trans_self _
  · intro v; rfl

/-- Symmetry of the shear-strip equivalence. -/
theorem S1487StripEquiv_symm (i j : SourceTheorem311Index) :
    FPrimeStripEquiv.symm (S1487StripEquiv i j) = S1487StripEquiv j i := by
  refine S1487StripEquiv_ext ?_ ?_ ?_
  · intro v; rfl
  · intro v
    ext x
    change ((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
        (sourceHaarActualShearMulEquiv j.1 j.2)).symm x =
      ((sourceHaarActualShearMulEquiv j.1 j.2).symm.trans
        (sourceHaarActualShearMulEquiv i.1 i.2)) x
    rw [MulEquiv.symm_trans_apply, MulEquiv.trans_apply]
    rfl
  · intro v; rfl

/-- Transitivity of the shear-strip equivalence. -/
theorem S1487StripEquiv_trans (i j k : SourceTheorem311Index) :
    FPrimeStripEquiv.trans (S1487StripEquiv i j) (S1487StripEquiv j k) =
      S1487StripEquiv i k := by
  refine S1487StripEquiv_ext ?_ ?_ ?_
  · intro v; rfl
  · intro v
    ext x
    change ((sourceHaarActualShearMulEquiv j.1 j.2).symm.trans
        (sourceHaarActualShearMulEquiv k.1 k.2))
        (((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
          (sourceHaarActualShearMulEquiv j.1 j.2)) x) =
      ((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
        (sourceHaarActualShearMulEquiv k.1 k.2)) x
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  · intro v; rfl

/-- The theater at a source index over a fixed arithmetic input. -/
def S1487Theater (A : InitialThetaArithmeticData.{0} l)
    (i : SourceTheorem311Index) : HodgeTheater.{0, 0, 0, 0} l S1487W where
  arithmetic := A
  primeStrip := S1487Strip i.1 i.2
  thetaPacket := sourceHaarActualThetaPacket l

/-- Extensionality for the theater links. -/
theorem S1487TheaterLink_ext
    {A : InitialThetaArithmeticData.{0} l} {i j : SourceTheorem311Index}
    {L M : HodgeTheaterLink (S1487Theater A i) (S1487Theater A j)}
    (h : L.primeStripEquiv = M.primeStripEquiv) : L = M := by
  cases L
  cases M
  simp only at h
  congr

/-- The canonical link between two shear theaters. -/
noncomputable def S1487TheaterLink (A : InitialThetaArithmeticData.{0} l)
    (i j : SourceTheorem311Index) :
    HodgeTheaterLink (S1487Theater A i) (S1487Theater A j) where
  primeStripEquiv := S1487StripEquiv i j
  theta_q_eq := rfl
  theta_scale_eq := by
    intro j
    rfl

theorem S1487TheaterLink_refl (A : InitialThetaArithmeticData.{0} l)
    (i : SourceTheorem311Index) :
    S1487TheaterLink A i i = HodgeTheaterLink.refl (S1487Theater A i) := by
  refine S1487TheaterLink_ext ?_
  exact S1487StripEquiv_self i

theorem S1487TheaterLink_symm (A : InitialThetaArithmeticData.{0} l)
    (i j : SourceTheorem311Index) :
    HodgeTheaterLink.symm (S1487TheaterLink A i j) = S1487TheaterLink A j i := by
  refine S1487TheaterLink_ext ?_
  exact S1487StripEquiv_symm i j

theorem S1487TheaterLink_trans (A : InitialThetaArithmeticData.{0} l)
    (i j k : SourceTheorem311Index) :
    HodgeTheaterLink.trans (S1487TheaterLink A i j) (S1487TheaterLink A j k) =
      S1487TheaterLink A i k := by
  refine S1487TheaterLink_ext ?_
  exact S1487StripEquiv_trans i j k

/-- Distinct indices give distinct theaters: the shear matrix entries recover
the index. -/
theorem S1487Theater_injective (A : InitialThetaArithmeticData.{0} l) :
    Function.Injective (S1487Theater (l := l) A) := by
  intro i j h
  have hprojHEq : HEq ((S1487Theater A i).primeStrip.proj S1487w0)
      ((S1487Theater A j).primeStrip.proj S1487w0) :=
    congr_arg_heq (fun T : HodgeTheater.{0, 0, 0, 0} l S1487W =>
      T.primeStrip.proj S1487w0) h
  have hproj : (S1487Theater A i).primeStrip.proj S1487w0 =
      (S1487Theater A j).primeStrip.proj S1487w0 := eq_of_heq hprojHEq
  have h01 := DFunLike.congr_fun hproj
    (Multiplicative.ofAdd ((0 : Int), (1 : Int)))
  have h10 := DFunLike.congr_fun hproj
    (Multiplicative.ofAdd ((1 : Int), (0 : Int)))
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

/-- The concrete shear family over the finite-prime index type. -/
noncomputable def S1487Family (A : InitialThetaArithmeticData.{0} l) :
    SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} l S1487W where
  index := SourceTheorem311Index
  theater := S1487Theater A
  distinct := S1487Theater_injective A
  link := S1487TheaterLink A
  link_refl := S1487TheaterLink_refl A
  link_symm := S1487TheaterLink_symm A
  link_trans := S1487TheaterLink_trans A
  permutation := Equiv.refl SourceTheorem311Index
  permutationLink := fun i => HodgeTheaterLink.refl (S1487Theater A i)
  permutation_naturality := by
    intro i j
    change HodgeTheaterLink.trans (S1487TheaterLink A i j)
        (HodgeTheaterLink.refl (S1487Theater A j)) =
      HodgeTheaterLink.trans (HodgeTheaterLink.refl (S1487Theater A i))
        (S1487TheaterLink A i j)
    rw [HodgeTheaterLink.trans_refl, HodgeTheaterLink.refl_trans]

/-- A concrete source input over the shear family, for any source datum with
the concrete Gaussian arithmetic. -/
noncomputable def S1487OriginalInput (S : SourceDefinition31Data.{0} l) :
    OriginalInput.{0, 0, 0, 0, 0} l S1487W where
  initial := S
  family := S1487Family S.arithmetic
  index_equiv := Equiv.refl SourceTheorem311Index
  arithmetic_alignment := by
    intro i
    rfl

/-! ## 3. The concrete Gaussian source data

A generic Definition 3.1 datum over the concrete Gaussian arithmetic, with the
bad-place family and its real q-parameters supplied explicitly.  The scalar
conclusions below use only the bad-place clause. -/

/-- The concrete Gaussian arithmetic input. -/
abbrev S1487Arithmetic (l : PrimeGeFive) : InitialThetaArithmeticData.{0} l :=
  concreteGaussianInitialThetaArithmeticData l

/-- Generic Definition 3.1 source datum over the concrete Gaussian arithmetic
with the bad-place q-parameters supplied explicitly. -/
noncomputable def S1487SourceData (Bad : Type) [Fintype Bad] (q : Bad → ℝ)
    (hq0 : ∀ b, q b ≠ 0) (hq1 : ∀ b, ‖q b‖ < 1) (hqne : ∀ b, q b ≠ 1) :
    SourceDefinition31Data.{0} l where
  arithmetic := S1487Arithmetic l
  selectedPlaces := Unit
  badPlaces := Bad
  reduction :=
    { partition :=
        { badIncluded := fun _ => ()
          selectedNonempty := ⟨()⟩
          badFinite := inferInstance
          selectedLabel := fun _ => 0
          badLabel := fun _ => 0
          badLabel_compatible := fun _ => rfl }
      stableReduction := fun _ => True
      stableReduction_proved := fun _ => trivial
      multiplicativeReduction := fun _ => True
      multiplicativeReduction_proved := fun _ => trivial
      splitMultiplicativeReduction := fun _ => True
      splitMultiplicativeReduction_proved := fun _ => trivial
      reductionCompatibility := fun _ _ => trivial
      qParameter := q
      qParameter_nonzero := hq0
      qParameter_contracting := hq1
      qParameter_reduction_compatibility := fun b _ => hqne b }
  torsion :=
    { torsionCarrier := Multiplicative (ZMod 6)
      torsionCarrierLaw := inferInstance
      torsionLabel := fun _ => 0
      torsionNonempty := ⟨1⟩
      representationCarrier := Multiplicative (ZMod 6)
      representationCarrierLaw := inferInstance
      representationGroup := Multiplicative (ZMod 6)
      representationGroupLaw := inferInstance
      representation := MonoidHom.id _
      representation_surjective := fun x => ⟨x, rfl⟩
      imageContainsSL2 := True
      imageContainsSL2_proved := trivial
      sixTorsionIndependent := True
      sixTorsionIndependent_proved := trivial
      lTorsionCompatible := True
      lTorsionCompatible_proved := trivial }
  orbicurve :=
    { curve := Unit
      puncturedCurve := Unit
      cover := Unit
      structureGroup := Unit
      structureGroupLaw := inferInstance
      curveToPunctured := id
      coverToPunctured := id
      cover_surjective := fun x => ⟨x, rfl⟩
      exactSequence :=
        { baseGroup := Unit
          coverGroup := Unit
          geometricGroup := Unit
          baseGroupLaw := inferInstance
          coverGroupLaw := inferInstance
          geometricGroupLaw := inferInstance
          injection := MonoidHom.id Unit
          projection := MonoidHom.id Unit
          injection_injective := fun a b _ => Subsingleton.elim a b
          projection_surjective := fun x => ⟨x, rfl⟩
          exact_at_cover := by intro x; simp }
      cuspCount := 1
      cuspCount_pos := by norm_num
      curveCompatibility := True
      curveCompatibility_proved := trivial }
  sections :=
    { valuationCarrier := Unit
      modifiedValuationCarrier := Unit
      localGroupCarrier := fun _ => Unit
      modifiedLocalGroupCarrier := fun _ => Unit
      sectionMap := id
      sectionRightInverse := id
      section_left_inverse := fun _ => rfl
      section_right_inverse := fun _ => rfl
      localGroupSection := fun _ x => x
      localGroupSection_injective := fun _ _ _ h => h
      localGroupSection_surjective := fun _ x => ⟨x, rfl⟩
      finitePlaceData := True
      finitePlaceData_proved := trivial
      infinitePlaceData := True
      infinitePlaceData_proved := trivial }
  cusp :=
    { epsilon := 1
      epsilon_positive := by norm_num
      epsilon_nonzero := by norm_num
      epsilon_compatibility := True
      epsilon_compatibility_proved := trivial
      cuspScale := 1
      cuspScale_positive := by norm_num
      epsilon_scale_relation := by norm_num }
  arithmetic_reduction_compatibility := True
  arithmetic_reduction_compatibility_proved := trivial
  arithmetic_torsion_compatibility := True
  arithmetic_torsion_compatibility_proved := trivial
  arithmetic_orbicurve_compatibility := True
  arithmetic_orbicurve_compatibility_proved := trivial
  arithmetic_section_compatibility := True
  arithmetic_section_compatibility_proved := trivial
  arithmetic_cusp_compatibility := True
  arithmetic_cusp_compatibility_proved := trivial

/-- The actual q parameters of the concrete Gaussian five place are legitimate
Definition 3.1(b) q-parameters: nonzero, contracting, and not one. -/
theorem S1487Cand_qParameter_nonzero : ‖S1487Cand.q‖ ≠ 0 :=
  ne_of_gt (qNorm_pos S1487Cand)

theorem S1487Cand_qParameter_contracting : ‖‖S1487Cand.q‖‖ < 1 := by
  rw [Real.norm_of_nonneg (le_of_lt (qNorm_pos S1487Cand))]
  exact qNorm_lt_one S1487Cand

theorem S1487Cand_qParameter_ne_one : ‖S1487Cand.q‖ ≠ 1 := by
  intro h
  have hlt := qNorm_lt_one S1487Cand
  rw [h] at hlt
  exact lt_irrefl 1 hlt

/-- The faithful one-place source datum: the bad-place q-parameter is the
actual completion q magnitude of the concrete Gaussian place. -/
noncomputable def S1487FaithfulSourceData : SourceDefinition31Data.{0} l :=
  S1487SourceData (l := l) PUnit (fun _ => ‖S1487Cand.q‖)
    (fun _ => S1487Cand_qParameter_nonzero)
    (fun _ => S1487Cand_qParameter_contracting)
    (fun _ => S1487Cand_qParameter_ne_one)

/-- The two-place source datum: two bad places, both with the actual completion
q magnitude of the concrete Gaussian place. -/
noncomputable def S1487TwoPlaceSourceData : SourceDefinition31Data.{0} l :=
  S1487SourceData (l := l) Bool (fun _ => ‖S1487Cand.q‖)
    (fun _ => S1487Cand_qParameter_nonzero)
    (fun _ => S1487Cand_qParameter_contracting)
    (fun _ => S1487Cand_qParameter_ne_one)

/-! ## 4. The concrete inputs and the concrete Gaussian C3 -/

/-- The concrete source input for the faithful one-place data. -/
noncomputable def S1487FaithfulInput :
    OriginalInput.{0, 0, 0, 0, 0} l S1487W :=
  S1487OriginalInput (l := l) S1487FaithfulSourceData

/-- The concrete source input for the two-place data. -/
noncomputable def S1487TwoPlaceInput :
    OriginalInput.{0, 0, 0, 0, 0} l S1487W :=
  S1487OriginalInput (l := l) S1487TwoPlaceSourceData

/-- The actual S1391 L-carrier C3 for the faithful input at the Gaussian five
place. -/
noncomputable def S1487FaithfulC3 :
    SourcePilotRegionDataL (l := l) (I := S1487FaithfulInput (l := l)) :=
  actualSourcePilotRegionDataL (l := l) (I := S1487FaithfulInput (l := l)) S1487FivePlace

/-- The actual S1391 L-carrier C3 for the two-place input at the Gaussian five
place. -/
noncomputable def S1487TwoPlaceC3 :
    SourcePilotRegionDataL (l := l) (I := S1487TwoPlaceInput (l := l)) :=
  actualSourcePilotRegionDataL (l := l) (I := S1487TwoPlaceInput (l := l)) S1487FivePlace

/-! ## 5. The single completion q side of C3

Both actual C3 records carry the same concrete q candidate, so the paper
q-pilot scalar is the negative of the actual local log magnitude. -/

theorem S1487FaithfulC3_q :
    (S1487FaithfulC3 (l := l)).q = S1487Cand := rfl

theorem S1487TwoPlaceC3_q :
    (S1487TwoPlaceC3 (l := l)).q = S1487Cand := rfl

/-- The paper q-pilot scalar of the actual Gaussian C3 is `-localLogMagnitude`. -/
theorem S1487FaithfulC3_logVolume :
    OrigXiFPaperQPilotLogVolume (S1487FaithfulC3 (l := l)) =
      -localLogMagnitude S1487Cand := by
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm, S1487FaithfulC3_q,
    localLogMagnitude, localSignedLog, neg_neg]
  rfl

theorem S1487TwoPlaceC3_logVolume :
    OrigXiFPaperQPilotLogVolume (S1487TwoPlaceC3 (l := l)) =
      -localLogMagnitude S1487Cand := by
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm, S1487TwoPlaceC3_q,
    localLogMagnitude, localSignedLog, neg_neg]
  rfl

/-! ## 6. The bad-place family sums -/

theorem S1487Faithful_sourceBadQAbsLog :
    sourceBadQAbsLog (S1487FaithfulSourceData (l := l)) =
      localLogMagnitude S1487Cand := by
  unfold sourceBadQAbsLog
  letI := (S1487FaithfulSourceData (l := l)).bad_finite
  change (∑ b : PUnit,
      |Real.log ((S1487FaithfulSourceData (l := l)).reduction.qParameter b)|) =
    localLogMagnitude S1487Cand
  rw [Fintype.sum_unique]
  exact abs_localSignedLog S1487Cand

theorem S1487TwoPlace_sourceBadQAbsLog :
    sourceBadQAbsLog (S1487TwoPlaceSourceData (l := l)) =
      2 * localLogMagnitude S1487Cand := by
  unfold sourceBadQAbsLog
  letI := (S1487TwoPlaceSourceData (l := l)).bad_finite
  change (∑ b : Bool,
      |Real.log ((S1487TwoPlaceSourceData (l := l)).reduction.qParameter b)|) =
    2 * localLogMagnitude S1487Cand
  rw [Fintype.sum_bool]
  have h : |Real.log ‖S1487Cand.q‖| = localLogMagnitude S1487Cand :=
    abs_localSignedLog S1487Cand
  show |Real.log ‖S1487Cand.q‖| + |Real.log ‖S1487Cand.q‖| =
    2 * localLogMagnitude S1487Cand
  rw [h]
  ring

/-! ## 7. The two answers -/

/-- **TRUE branch.**  For the faithful one-place bad family the O-layer scalar
equality holds: the bad-family sum is exactly the single completion q
magnitude of the concrete Gaussian C3. -/
theorem S1487FaithfulScalarEq :
    OrigXiFPaperQPilotScalarExactFirstField (I := S1487FaithfulInput (l := l))
      (S1487FaithfulC3 (l := l)) := by
  unfold OrigXiFPaperQPilotScalarExactFirstField sourceQPilotSignedLog
  rw [S1487FaithfulC3_logVolume]
  change -sourceBadQAbsLog (S1487FaithfulSourceData (l := l)) =
    -localLogMagnitude S1487Cand
  rw [S1487Faithful_sourceBadQAbsLog]

/-- **FALSE branch (actual counterexample).**  For the two-place bad family the
bad-family sum double-counts the actual completion q magnitude, so the O-layer
scalar equality fails. -/
theorem S1487TwoPlaceScalarNe :
    ¬ OrigXiFPaperQPilotScalarExactFirstField (I := S1487TwoPlaceInput (l := l))
      (S1487TwoPlaceC3 (l := l)) := by
  intro h
  unfold OrigXiFPaperQPilotScalarExactFirstField sourceQPilotSignedLog at h
  rw [S1487TwoPlaceC3_logVolume] at h
  change -sourceBadQAbsLog (S1487TwoPlaceSourceData (l := l)) =
    -localLogMagnitude S1487Cand at h
  rw [S1487TwoPlace_sourceBadQAbsLog] at h
  have hpos := S1487Cand_magnitude_pos
  linarith


/-! ## 7b. An explicit rational counterexample: two bad places with q = 1/2

The same concrete Gaussian C3, but the bad-place q-parameters are the explicit
rational number `1/2` (nonzero, contracting, not one: a legitimate Definition
3.1(b) parameter).  Then the bad-family sum is `2 * |log (1/2)| = log 4`, while
the single completion q side is `-order * log 5` with `order >= 1`, hence at
most `-log 5`.  Since `log 4 < log 5`, the two scalars differ numerically. -/

/-- The explicitly rational two-place source datum. -/
noncomputable def S1487HalfSourceData : SourceDefinition31Data.{0} l :=
  S1487SourceData (l := l) Bool (fun _ => (1 : ℝ) / 2)
    (fun _ => by norm_num)
    (fun _ => by norm_num)
    (fun _ => by norm_num)

/-- The concrete source input for the rational two-place data. -/
noncomputable def S1487HalfInput :
    OriginalInput.{0, 0, 0, 0, 0} l S1487W :=
  S1487OriginalInput (l := l) S1487HalfSourceData

/-- The actual S1391 L-carrier C3 for the rational two-place input. -/
noncomputable def S1487HalfC3 :
    SourcePilotRegionDataL (l := l) (I := S1487HalfInput (l := l)) :=
  actualSourcePilotRegionDataL (l := l) (I := S1487HalfInput (l := l))
    S1487FivePlace

theorem S1487HalfC3_logVolume :
    OrigXiFPaperQPilotLogVolume (S1487HalfC3 (l := l)) =
      -localLogMagnitude S1487Cand := by
  have hq : (S1487HalfC3 (l := l)).q = S1487Cand := rfl
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm, hq,
    localLogMagnitude, localSignedLog, neg_neg]
  rfl

/-- The bad-family sum of the rational two-place data is exactly `log 4`. -/
theorem S1487Half_sourceBadQAbsLog :
    sourceBadQAbsLog (S1487HalfSourceData (l := l)) = Real.log 4 := by
  unfold sourceBadQAbsLog
  letI := (S1487HalfSourceData (l := l)).bad_finite
  change (∑ b : Bool,
      |Real.log ((S1487HalfSourceData (l := l)).reduction.qParameter b)|) =
    Real.log 4
  rw [Fintype.sum_bool]
  have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have habs : |Real.log ((1 : ℝ) / 2)| = Real.log 2 := by
    rw [hlog, abs_neg, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  show |Real.log ((1 : ℝ) / 2)| + |Real.log ((1 : ℝ) / 2)| = Real.log 4
  rw [habs]
  have hmul : Real.log 4 = Real.log 2 + Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-- **Second explicit counterexample.**  For the rational two-place data the
O-layer scalar equality fails already numerically: `-log 4` against at most
`-log 5`. -/
theorem S1487HalfScalarNe :
    ¬ OrigXiFPaperQPilotScalarExactFirstField (I := S1487HalfInput (l := l))
      (S1487HalfC3 (l := l)) := by
  intro h
  unfold OrigXiFPaperQPilotScalarExactFirstField sourceQPilotSignedLog at h
  rw [S1487HalfC3_logVolume] at h
  change -sourceBadQAbsLog (S1487HalfSourceData (l := l)) =
    -localLogMagnitude S1487Cand at h
  rw [S1487Half_sourceBadQAbsLog] at h
  have hge := S1487Cand_magnitude_ge_log_five
  have hlt : Real.log 4 < Real.log 5 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ## 8. The O-layer `scalar_eq` field of S1463 -/

/-- The O-layer `scalar_eq` field, restated through the object's own
`qPilotLogVolume_eq`. -/
theorem S1487_origXiFScalarExactField_iff
    {G : Type uG} [Group G] [TopologicalSpace G]
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {envStrip : FPrimeStrip S1487W}
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      (S1487TwoPlaceInput (l := l)) G envStrip)
    (C3 : SourcePilotRegionDataL (l := l) (I := S1487TwoPlaceInput (l := l))) :
    OrigXiFThetaLinkActualScalarExactField O C3 ↔
      sourceQPilotSignedLog (S1487TwoPlaceInput (l := l)).initial =
        OrigXiFPaperQPilotLogVolume C3 := by
  unfold OrigXiFThetaLinkActualScalarExactField
  rw [O.qPilotLogVolume_eq]

/-- **No O-layer q-pilot object satisfies `scalar_eq` at the two-place
concrete Gaussian data and its actual C3.** -/
theorem S1487_no_origXiFScalarExactField
    {G : Type uG} [Group G] [TopologicalSpace G]
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {envStrip : FPrimeStrip S1487W}
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      (S1487TwoPlaceInput (l := l)) G envStrip) :
    ¬ OrigXiFThetaLinkActualScalarExactField O
      (S1487TwoPlaceC3 (l := l)) := by
  intro h
  have h' := (S1487_origXiFScalarExactField_iff (l := l) O
    (S1487TwoPlaceC3 (l := l))).mp h
  exact S1487TwoPlaceScalarNe (l := l) (by
    unfold OrigXiFPaperQPilotScalarExactFirstField
    exact h')

/-- Conversely, at the faithful one-place data the O-layer `scalar_eq` field
holds for every q-pilot object. -/
theorem S1487_origXiFScalarExactField_faithful
    {G : Type uG} [Group G] [TopologicalSpace G]
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {envStrip : FPrimeStrip S1487W}
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      (S1487FaithfulInput (l := l)) G envStrip) :
    OrigXiFThetaLinkActualScalarExactField O
      (S1487FaithfulC3 (l := l)) := by
  unfold OrigXiFThetaLinkActualScalarExactField
  rw [O.qPilotLogVolume_eq]
  exact S1487FaithfulScalarEq (l := l)

/-! ## 9. Axiom probes -/

#print axioms S1487FaithfulScalarEq
#print axioms S1487TwoPlaceScalarNe
#print axioms S1487_no_origXiFScalarExactField
#print axioms S1487_origXiFScalarExactField_faithful
#print axioms S1487Faithful_sourceBadQAbsLog
#print axioms S1487TwoPlace_sourceBadQAbsLog
#print axioms S1487HalfScalarNe
#print axioms S1487Half_sourceBadQAbsLog

end LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual

end
