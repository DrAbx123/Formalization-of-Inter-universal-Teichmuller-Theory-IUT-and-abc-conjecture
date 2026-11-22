import tmp.sheaf.xif.paper.PaperSourceGeometryActual

-- Actual q/theta geometry constructor
--
-- CompletionValuedSourceGeometry now carries an actual q unit in each local
-- completion and an actual FiniteThetaPacket, with a proof that the theta
-- packet q is the norm of the q unit. This file supplies the actual
-- constructor from those data; no Classical.choice q is used.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperSourceGeometryQActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v}

-- Actual geometry from supplied q units and theta packet, with the actual
-- q/theta consistency proof.
noncomputable def completionValuedSourceGeometryOfQ
    (place : V → FinitePlaceAtPrime K p)
    (qUnit : (v : V) → CompletionValueCarrier (place v))
    (thetaPacket : FiniteThetaPacket l)
    (thetaPacket_q_eq : ∀ v : V,
      thetaPacket.q = ‖(qUnit v : CommonPrimeCompletion (place v))‖) :
    CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V where
  place := place
  qUnit := qUnit
  thetaPacket := thetaPacket
  thetaPacket_q_eq := thetaPacket_q_eq

theorem completionValuedSourceGeometryOfQ_place
    (place : V → FinitePlaceAtPrime K p)
    (qUnit : (v : V) → CompletionValueCarrier (place v))
    (thetaPacket : FiniteThetaPacket l)
    (thetaPacket_q_eq : ∀ v : V,
      thetaPacket.q = ‖(qUnit v : CommonPrimeCompletion (place v))‖)
    (v : V) :
    ((completionValuedSourceGeometryOfQ (l := l) place qUnit thetaPacket
      thetaPacket_q_eq).place v) = place v := rfl

theorem completionValuedSourceGeometryOfQ_qUnit
    (place : V → FinitePlaceAtPrime K p)
    (qUnit : (v : V) → CompletionValueCarrier (place v))
    (thetaPacket : FiniteThetaPacket l)
    (thetaPacket_q_eq : ∀ v : V,
      thetaPacket.q = ‖(qUnit v : CommonPrimeCompletion (place v))‖)
    (v : V) :
    ((completionValuedSourceGeometryOfQ (l := l) place qUnit thetaPacket
      thetaPacket_q_eq).qUnit v) = qUnit v := rfl

theorem completionValuedSourceGeometryOfQ_thetaPacket_q_eq
    (place : V → FinitePlaceAtPrime K p)
    (qUnit : (v : V) → CompletionValueCarrier (place v))
    (thetaPacket : FiniteThetaPacket l)
    (thetaPacket_q_eq : ∀ v : V,
      thetaPacket.q = ‖(qUnit v : CommonPrimeCompletion (place v))‖)
    (v : V) :
    (completionValuedSourceGeometryOfQ (l := l) place qUnit thetaPacket
      thetaPacket_q_eq).thetaPacket.q =
      ‖(qUnit v : CommonPrimeCompletion (place v))‖ := by
  exact thetaPacket_q_eq v

theorem completionValuedSourceGeometryOfQ_thetaPacket_q_pos
    (place : V → FinitePlaceAtPrime K p)
    (qUnit : (v : V) → CompletionValueCarrier (place v))
    (thetaPacket : FiniteThetaPacket l)
    (thetaPacket_q_eq : ∀ v : V,
      thetaPacket.q = ‖(qUnit v : CommonPrimeCompletion (place v))‖)
    (v : V) :
    0 < (completionValuedSourceGeometryOfQ (l := l) place qUnit thetaPacket
      thetaPacket_q_eq).thetaPacket.q := by
  rw [completionValuedSourceGeometryOfQ_thetaPacket_q_eq]
  exact norm_pos_iff.mpr (Units.ne_zero (qUnit v))

#check completionValuedSourceGeometryOfQ
#check completionValuedSourceGeometryOfQ_place
#check completionValuedSourceGeometryOfQ_qUnit
#check completionValuedSourceGeometryOfQ_thetaPacket_q_eq
#check completionValuedSourceGeometryOfQ_thetaPacket_q_pos

end LeanFormal.IUT.XiFPaper.PaperSourceGeometryQActual

end