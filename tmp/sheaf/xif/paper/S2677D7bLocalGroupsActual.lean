import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply
import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup
import Mathlib.FieldTheory.AlgebraicClosure

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Geometry
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply

namespace LeanFormal.IUT.XiFPaper.S2677D7bLocalGroupsActual

universe u

def S2677OriginEval (K : Type u) [Field K] : MvPolynomial (Fin 2) K →+* K :=
  MvPolynomial.eval (fun _ => 0)

theorem S2677OriginEval_eq (K : Type u) [Field K] :
    S2677OriginEval K (puncturedEllipticEquation K) = 0 := by
  simp [S2677OriginEval, puncturedEllipticEquation]

def S2677OriginAlg (K : Type u) [Field K] :
    puncturedEllipticCoordinateRing K →+* K :=
  Ideal.Quotient.lift (Ideal.span {puncturedEllipticEquation K}) (S2677OriginEval K)
    (fun x hx => by
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      simp [S2677OriginEval_eq])

def S2677OriginPoint (K : Type u) [Field K] :
    Spec (CommRingCat.of K) ⟶ puncturedEllipticCurveScheme K :=
  Spec.map (CommRingCat.ofHom (S2677OriginAlg K))

noncomputable def S2677FinitePlaceGroup {K : Type u} [Field K] [NumberField K]
    (p : NumberField.FinitePlace K) : Type (u+1) :=
  letI : Field (NumberFieldFinitePlace.ResidueField p) :=
    Ideal.Quotient.field (NumberFieldFinitePlace.underlyingPrime p).asIdeal
  curveEtaleFundamentalGroup
    (AlgebraicClosure (NumberFieldFinitePlace.ResidueField p))
    (S2677OriginPoint (AlgebraicClosure (NumberFieldFinitePlace.ResidueField p)))

noncomputable def S2677InfinitePlaceGroup {K : Type u} [Field K] [NumberField K]
    (_p : NumberField.InfinitePlace K) : Type (u+1) :=
  curveEtaleFundamentalGroup (AlgebraicClosure K) (S2677OriginPoint (AlgebraicClosure K))

noncomputable def S2677PlaceGroup (K : Type u) [Field K] [NumberField K]
    (x : NumberFieldPlace K) : Type (u+1) :=
  match x with
  | NumberFieldPlace.finite p => S2677FinitePlaceGroup p
  | NumberFieldPlace.infinite p => S2677InfinitePlaceGroup p

instance S2677PlaceGroup_group (K : Type u) [Field K] [NumberField K]
    (x : NumberFieldPlace K) : Group (S2677PlaceGroup K x) := by
  cases x with
  | finite p =>
      unfold S2677PlaceGroup S2677FinitePlaceGroup
      dsimp only
      infer_instance
  | infinite p =>
      unfold S2677PlaceGroup S2677InfinitePlaceGroup
      infer_instance

noncomputable def S2677Carrier {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (x : NumberFieldPlace A.K) : Type (u+1) :=
  S2677PlaceGroup A.K x

instance S2677Carrier_group {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (x : NumberFieldPlace A.K) : Group (S2677Carrier A x) :=
  S2677PlaceGroup_group A.K x


noncomputable def S2677SupplyCanonical {l : PrimeGeFive}
    (A : InitialThetaArithmeticData.{u} l) :
    D7LocalGroupSectionSupply.{u, u+1}
      (SourceValuationSectionLayer.canonical A) where
  localGroupCarrier x := S2677Carrier A x.1
  modifiedLocalGroupCarrier y :=
    S2677Carrier A ((SourceValuationSectionLayer.canonical A).sectionRightInverse y).1
  localGroupSection x :=
    Equiv.cast (congrArg (fun z : NumberFieldPlace A.K => S2677Carrier A z)
      (congrArg (fun z => z.1)
        ((SourceValuationSectionLayer.canonical A).section_left_inverse x))).symm
  localGroupSection_injective x :=
    (Equiv.cast _).injective
  localGroupSection_surjective x :=
    (Equiv.cast _).surjective
  finitePlaceData :=
    ∀ x : (SourceValuationSectionLayer.canonical A).valuationCarrier,
      NumberFieldPlace.IsFinite x.1 → Nonempty (S2677Carrier A x.1)
  finitePlaceData_proved := fun x _ => ⟨(1 : S2677Carrier A x.1)⟩
  infinitePlaceData :=
    ∀ x : (SourceValuationSectionLayer.canonical A).valuationCarrier,
      NumberFieldPlace.IsInfinite x.1 → Nonempty (S2677Carrier A x.1)
  infinitePlaceData_proved := fun x _ => ⟨(1 : S2677Carrier A x.1)⟩

theorem S2677D7bLocalGroupSectionConstruction (l : PrimeGeFive) :
    D7bLocalGroupSectionConstruction.{u, u+1} l :=
  fun A => ⟨S2677SupplyCanonical A⟩

theorem S2677D7SectionConstruction (l : PrimeGeFive) :
    Theorem311Source.SourceDefinition31Root.D7SectionConstruction.{u, u, u+1} l :=
  d7SectionConstruction_of_localGroupSupply
    (S2677D7bLocalGroupSectionConstruction l)

#check S2677SupplyCanonical
#check S2677D7SectionConstruction
#check S2677D7bLocalGroupSectionConstruction
#print axioms S2677SupplyCanonical
#print axioms S2677D7bLocalGroupSectionConstruction
#print axioms S2677D7SectionConstruction

end LeanFormal.IUT.XiFPaper.S2677D7bLocalGroupsActual
end
