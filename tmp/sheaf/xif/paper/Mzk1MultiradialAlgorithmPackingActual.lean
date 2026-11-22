import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithmReduction
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialIplLinkWiring
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT

/-! Mainline (A482 rung R1): BPS x etHT -> MultiradialRep algorithm packing.
  Reuses the tree presentation/algorithm records (SourceMultiradialPresentationWiring),
  the reduced IPL link (SourceMultiradialIplLinkWiring) and the APT/SHE landing
  (StepXI/APT).  Proves the algorithm is total with output invariant, the APT property,
  the reduced IPL property and the (Ind1) functoriality law. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1MultiradialAlgorithmPackingActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.MultiradialAlgorithmReduction
open LeanFormal.IUT.SourceMultiradialPresentationWiring
open LeanFormal.IUT.SourceMultiradialIplLinkWiring

noncomputable section

universe u v uG1 uG2 ua uv upi umon ui uOut

variable {l : PrimeGeFive} {V : Type uv}
variable {G1 : Type uG1} [Group G1] {G2 : Type uG2} [Group G2]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n : Int}
variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- R1 input data: BPS stage data (`carrier`), etHT stage data (procession
  automorphism/Ind2 actions and the algorithm input), and the SHE landing datum. -/
structure MultiradialAlgorithmData (S : SourceOneColumnArithmeticHolomorphicStructure V) where
  carrier : ParametricTheorem311.Carrier Label Choice
  autom : SourceProcessionAutomorphismData carrier G1
  ind2 : Ind2ActionData carrier autom G2
  input : ParametricTheorem311.AlgorithmInput carrier
  landing : SourceLocalizationExpressible S Choice

/-- R1 packing: `multiradialAlgorithm : BPS x etHT -> MultiradialRep` (the tree
  multiradial algorithm record). -/
def multiradialAlgorithm {S : SourceOneColumnArithmeticHolomorphicStructure V}
    (D : MultiradialAlgorithmData (V := V) (G1 := G1) (G2 := G2)
      (Label := Label) (Choice := Choice) S) :
    SourceTheorem311MultiradialAlgorithm G1 G2 I n Choice :=
  sourceAlgorithmOfCarrier D.carrier D.autom D.ind2 D.input

/-- R1 output invariant: the presented output is the algorithm run target. -/
theorem multiradialAlgorithm_output {S : SourceOneColumnArithmeticHolomorphicStructure V}
    (D : MultiradialAlgorithmData (V := V) (G1 := G1) (G2 := G2)
      (Label := Label) (Choice := Choice) S) :
    (multiradialAlgorithm (l := l) (I := I) (n := n) D).presentation.output =
      (ParametricTheorem311.runAlgorithm D.carrier D.input).target :=
  sourcePresentationOfCarrier_output D.carrier D.autom D.input

/-- R1 APT property: the packed algorithm admits the reflexive algorithmic parallel
  transport through its SHE landing datum (StepXI/APT). -/
theorem multiradialAlgorithm_apt {S : SourceOneColumnArithmeticHolomorphicStructure V}
    (D : MultiradialAlgorithmData (V := V) (G1 := G1) (G2 := G2)
      (Label := Label) (Choice := Choice) S) :
    SourceAPTStatement S
      (multiradialAlgorithm (l := l) (I := I) (n := n) D)
      (multiradialAlgorithm (l := l) (I := I) (n := n) D) :=
  ⟨SourceAlgorithmicParallelTransport.reflexive _ D.landing⟩

/-- R1 IPL property: the reduced (IPL) link holds for the packed algorithm input. -/
theorem multiradialAlgorithm_ipl {S : SourceOneColumnArithmeticHolomorphicStructure V}
    (D : MultiradialAlgorithmData (V := V) (G1 := G1) (G2 := G2)
      (Label := Label) (Choice := Choice) S) :
    ReducedIplLink D.carrier D.autom D.input :=
  reducedIplLink_holds D.carrier D.autom D.input

/-- R1 (Ind1) functoriality: the packed algorithm commutes with the procession
  automorphisms on route targets. -/
theorem multiradialAlgorithm_ind1_functorial
    {S : SourceOneColumnArithmeticHolomorphicStructure V}
    (D : MultiradialAlgorithmData (V := V) (G1 := G1) (G2 := G2)
      (Label := Label) (Choice := Choice) S)
    (g : G1) (route : List (RouteStep Label)) (c : Choice) :
    D.autom.act g (ParametricTheorem311.routeTarget D.carrier route c) =
      ParametricTheorem311.routeTarget D.carrier route (D.autom.act g c) :=
  automorphism_routeTarget D.carrier D.autom g route c

end

end LeanFormal.IUT.XiFPaper.Mzk1MultiradialAlgorithmPackingActual