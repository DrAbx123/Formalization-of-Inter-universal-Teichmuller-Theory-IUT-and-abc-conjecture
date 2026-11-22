import tmp.sheaf.xif.paper.RefLANACor312ProcessionActual
import tmp.sheaf.xif.paper.RefLANAPacketPresentationActual
import tmp.sheaf.xif.paper.RefLANAHodgeLabelsActual

/-! Mainline (A517-7): the Theorem 3.11 Cor 3.12-side object layer, built on the GREEN
self-contained reference copies: `RefLANACor312ProcessionActual` (label sets/capsules/
processions and the standard procession), `RefLANAPacketPresentationActual` (direct-sum-of-
fields packet presentation, integral/product/Borel/scaled-integral/hull regions) and
`RefLANAHodgeLabelsActual` (the ±-labels, geometric symmetry group and the Pm/Star torsors).
Every declaration below is a re-export or a direct bundle of those real copies. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RefCor312ObjectsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! ## 1. Processions and capsules (tensor-packet index data) -/

section ProcessionData

variable (ι : Type)

/-- The label set `S_{j+1} = {0,…,j}` of the tensor-packet construction. -/
abbrev Thm311ProcLabels (j : ℕ) : Finset ℕ := Iut.procLabels j

/-- A capsule of labels. -/
abbrev Thm311Capsule := Iut.Capsule ι

/-- An increasing chain of capsules (the index data of the tensor packets). -/
abbrev Thm311RefProcession := Iut.Procession ι

/-- The standard procession `S_2 ⊆ S_3 ⊆ ⋯ ⊆ S_{n+1}` (n = ℓ*). -/
def Thm311StandardProcession (n : ℕ) : Iut.Procession ℕ :=
  Iut.Procession.standard n

theorem thm311StandardProcession_length (n : ℕ) :
    (Thm311StandardProcession n).length = n :=
  Iut.Procession.standard_length n

theorem thm311StandardProcession_capsule_card (n : ℕ) (i : Fin n) :
    ((Thm311StandardProcession n).capsule i).card = i + 2 :=
  Iut.Procession.standard_capsule_card n i

/-- The inclusion map of label types between two capsules of a procession. -/
def thm311ProcessionInclusion (P : Iut.Procession ι) {i j : Fin P.length} (h : i ≤ j) :
    (P.capsule i).LabelType → (P.capsule j).LabelType :=
  P.inclusion h

end ProcessionData

/-! ## 2. Tensor packets as direct-sum-of-fields presentations -/

section PacketData

variable {C : Type} (P : Iut.DirectSumPresentation C)

/-- **O3 object**: the packet total space (the product over the finite component index). -/
abbrev Thm311PacketTotal := P.Total

/-- The holomorphic integral region `⊕_c O_c` of the packet. -/
def thm311PacketIntegralRegion : Set P.Total := P.integralRegion

/-- A direct-product region of the packet. -/
def thm311PacketIsProductRegion (R : Set P.Total) : Prop := P.IsProductRegion R

/-- The product region attached to component regions. -/
def thm311PacketProductRegion (U : ∀ c, Set (P.Summand c)) : Set P.Total :=
  P.productRegion U

/-- A Borel region of the packet. -/
def thm311PacketIsBorelRegion (R : Set P.Total) : Prop := P.IsBorelRegion R

/-- The scaled integral region `a·O` (candidate holomorphic hulls). -/
def thm311PacketScaledIntegral (a : P.Total) : Set P.Total := P.scaledIntegral a

/-- A hull region `a·O` with all components units. -/
def thm311PacketIsHullRegion (R : Set P.Total) : Prop := P.IsHullRegion R

theorem thm311Packet_mem_integralRegion {x : P.Total} :
    x ∈ thm311PacketIntegralRegion P ↔ ∀ c, x c ∈ P.integral c :=
  Iut.DirectSumPresentation.mem_integralRegion

theorem thm311Packet_mem_productRegion {U : ∀ c, Set (P.Summand c)} {x : P.Total} :
    x ∈ thm311PacketProductRegion P U ↔ ∀ c, x c ∈ U c :=
  Iut.DirectSumPresentation.mem_productRegion

theorem thm311Packet_isProductRegion_integral :
    thm311PacketIsProductRegion P (thm311PacketIntegralRegion P) :=
  P.isProductRegion_integralRegion

theorem thm311Packet_isProductRegion_scaled (a : P.Total) :
    thm311PacketIsProductRegion P (thm311PacketScaledIntegral P a) :=
  P.isProductRegion_scaledIntegral a

theorem thm311Packet_isHullRegion_integral :
    thm311PacketIsHullRegion P (thm311PacketIntegralRegion P) :=
  P.isHullRegion_integralRegion

end PacketData

/-! ## 3. Label torsors (re-exported from the green copy) -/

section Labels

open Iut.HodgeTheater

variable (ℓ : ℕ) [OddPrime ℓ]

theorem thm311Ref_card_flStar : Nat.card (FlStar ℓ) = ellStar ℓ :=
  card_flStar ℓ

theorem thm311Ref_card_absFl : Nat.card (AbsFl ℓ) = ellPm ℓ :=
  card_absFl ℓ

theorem thm311Ref_card_flSemi : Nat.card (FlSemi ℓ) = 2 * ℓ :=
  card_flSemi ℓ

def thm311Ref_pmIsoEquiv (A B : PmTorsor ℓ) : PmTorsor.Iso A B ≃ ℤˣ × ZMod ℓ :=
  PmTorsor.isoEquiv A B

theorem thm311Ref_pmIso_card (A B : PmTorsor ℓ) :
    Nat.card (PmTorsor.Iso A B) = 2 * ℓ :=
  PmTorsor.card_iso A B

def thm311Ref_starIsoEquiv (A B : StarTorsor ℓ) : StarTorsor.Iso A B ≃ FlStar ℓ :=
  StarTorsor.isoEquiv A B

theorem thm311Ref_starIso_card (A B : StarTorsor ℓ) :
    Nat.card (StarTorsor.Iso A B) = ellStar ℓ :=
  StarTorsor.card_iso A B

end Labels

end

end LeanFormal.IUT.XiFPaper.Mzk1RefCor312ObjectsActual