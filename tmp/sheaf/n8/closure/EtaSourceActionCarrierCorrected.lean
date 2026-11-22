import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellXMuPacket
import tmp.sheaf.n8.closure.C10BridgeProof

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# ETA source-action carrier corrected

Uses the actual SourceLGPProcession indices ind1/ind2 as a Label action on the
procession carrier Choice, and SourcePacketRealization logVolume/determinant/
possibleImage invariance as packet compatibility.  No field multiplication on
the additive log-shell K is used.

Exact gap: no actual SourceLGPProcession is constructed from the native
N8NativeInput X; the canonical construction needs SourceDefinition31Data, which
the native root does not supply (C10 bridge no-go).
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge

namespace LeanFormal.IUT.N8Closure.EtaSourceActionCarrierCorrected

universe u v w

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice]
  (P : SourceLGPProcession l Label Choice)

/-- ind1 as an equivalence of the procession carrier. -/
noncomputable def lgpInd1Equiv (g : Label) : Choice ≃ Choice where
  toFun c := P.ind1 g c
  invFun c := P.ind1 (-g) c
  left_inv c := by
    change P.ind1 (-g) (P.ind1 g c) = c
    rw [← P.ind1_add, add_neg_cancel, P.ind1_zero]
  right_inv c := by
    change P.ind1 g (P.ind1 (-g) c) = c
    rw [← P.ind1_add, neg_add_cancel, P.ind1_zero]

/-- ind2 as an equivalence of the procession carrier. -/
noncomputable def lgpInd2Equiv (g : Label) : Choice ≃ Choice where
  toFun c := P.ind2 g c
  invFun c := P.ind2 (-g) c
  left_inv c := by
    change P.ind2 (-g) (P.ind2 g c) = c
    rw [← P.ind2_add, add_neg_cancel, P.ind2_zero]
  right_inv c := by
    change P.ind2 g (P.ind2 (-g) c) = c
    rw [← P.ind2_add, neg_add_cancel, P.ind2_zero]

/-! ## Actual LGP carrier action package (right action) -/

/-- Actual LGP carrier action package: the additive Label group acts on the
procession carrier by ind1/ind2 (right action), with the actual laws. -/
structure LGPSourceActionCarrier (P : SourceLGPProcession l Label Choice) where
  procession : SourceLGPProcession l Label Choice
  action1 : Label → Choice ≃ Choice
  action1_eq : action1 = lgpInd1Equiv procession
  action1_zero : action1 0 = 1
  action1_add : ∀ g h c, action1 (g + h) c = action1 h (action1 g c)
  action2 : Label → Choice ≃ Choice
  action2_eq : action2 = lgpInd2Equiv procession
  action2_zero : action2 0 = 1
  action2_add : ∀ g h c, action2 (g + h) c = action2 h (action2 g c)

noncomputable def lgpSourceActionCarrier : LGPSourceActionCarrier P where
  procession := P
  action1 := lgpInd1Equiv P
  action1_eq := rfl
  action1_zero := by
    ext c
    exact P.ind1_zero c
  action1_add g h c := by
    change P.ind1 (g + h) c = P.ind1 h (P.ind1 g c)
    rw [P.ind1_add]
  action2 := lgpInd2Equiv P
  action2_eq := rfl
  action2_zero := by
    ext c
    exact P.ind2_zero c
  action2_add g h c := by
    change P.ind2 (g + h) c = P.ind2 h (P.ind2 g c)
    rw [P.ind2_add]

theorem lgpSourceActionCarrier_laws :
    (lgpSourceActionCarrier P).action1 0 = 1 ∧
      (∀ g h c, (lgpSourceActionCarrier P).action1 (g + h) c =
        (lgpSourceActionCarrier P).action1 h
          ((lgpSourceActionCarrier P).action1 g c)) ∧
      (lgpSourceActionCarrier P).action2 0 = 1 ∧
      (∀ g h c, (lgpSourceActionCarrier P).action2 (g + h) c =
        (lgpSourceActionCarrier P).action2 h
          ((lgpSourceActionCarrier P).action2 g c)) :=
  ⟨(lgpSourceActionCarrier P).action1_zero,
   (lgpSourceActionCarrier P).action1_add,
   (lgpSourceActionCarrier P).action2_zero,
   (lgpSourceActionCarrier P).action2_add⟩

namespace PacketCompatibility

variable (Q : SourcePacketRealization P)

/-- Actual packet compatibility: logVolume and determinant are ind1 invariant. -/
theorem packet_ind1_compat (g : Label) (c : Choice) :
    Q.logVolume (P.ind1 g c) = Q.logVolume c ∧
      Q.determinant (P.ind1 g c) = Q.determinant c :=
  ⟨Q.ind1_volume g c, Q.ind1_determinant g c⟩

/-- Actual packet compatibility: ind2 invariance. -/
theorem packet_ind2_compat (g : Label) (c : Choice) :
    Q.logVolume (P.ind2 g c) = Q.logVolume c ∧
      Q.determinant (P.ind2 g c) = Q.determinant c :=
  ⟨Q.ind2_volume g c, Q.ind2_determinant g c⟩

end PacketCompatibility

/-- Exact gap: no actual SourceLGPProcession is constructed from the native
N8NativeInput X.  The canonical procession construction requires
SourceDefinition31Data, which the native root does not supply. -/
def MissingNativeLGPProcession : Prop :=
  ∀ (X : N8NativeInput l),
    Nonempty (SourceDefinition31Data.{u} l)

end LeanFormal.IUT.N8Closure.EtaSourceActionCarrierCorrected

end