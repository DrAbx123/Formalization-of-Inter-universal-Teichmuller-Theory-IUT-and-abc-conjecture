/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.HodgeTheater.HodgeTheater
import tmp.sheaf.lana.iut.Iut.HodgeTheater.Procession

/-!
# Mzk1LANAHodgeThetaObjectActual — LANA Hodge-theater object (3.11 object side)

A515: reference object from LANA's actual `Θ^{±ell}NF`-Hodge theaters
(`Iut.HodgeTheater.HodgeTheater`, Definitions 6.11/6.13): the D-Θ^{±ell}NF
theater, its `{±1}`-torsor of isomorphisms (`card_iso`), and the standard model.
Also references the actual processions `prcPm`/`prcStar` from
`Iut.HodgeTheater.Procession` (IUT I Prop. 4.11/6.9).

No new axiom, no comparison, no shell. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAHodgeThetaObjectActual

open Iut
universe u

variable {ℓ : ℕ} [OddPrime ℓ] {V : Type u}

/-- The LANA `D-Θ^{±ell}NF`-Hodge theater object (Definition 6.13(ii)). -/
structure HodgeThetaNFObject where
  /-- the actual Hodge theater. -/
  theater : DThetaPmEllNFHT ℓ V

/-- The standard LANA model theater. -/
noncomputable def hodgeThetaNFObject : HodgeThetaNFObject (ℓ := ℓ) (V := V) where
  theater := DThetaPmEllNFHT.model

/-- `_constructed`: the object's theater is the LANA standard model. -/
theorem hodgeThetaNFObject_constructed :
    (hodgeThetaNFObject (ℓ := ℓ) (V := V)).theater = DThetaPmEllNFHT.model := rfl

/-- The isomorphisms of the actual Hodge theaters form a `{±1}`-torsor. -/
theorem hodgeTheta_iso_card (A B : DThetaPmEllNFHT ℓ V) :
    Nat.card (A.Iso B) = 2 := DThetaPmEllNFHT.card_iso A B

/-- The isomorphism torsor is `Zˣ`. -/
noncomputable def hodgeTheta_isoEquiv (A B : DThetaPmEllNFHT ℓ V) :
    A.Iso B ≃ ℤˣ := DThetaPmEllNFHT.isoEquiv A B

/-- The `ℓ±`-procession of the theater. -/
noncomputable def hodgeTheta_procPm (A : DThetaPmEllNFHT ℓ V) :
    Procession (AbsFl ℓ) := DThetaPmEllNFHT.procPm A

#check hodgeThetaNFObject_constructed
#check hodgeTheta_iso_card

end LeanFormal.IUT.XiFPaper.Mzk1LANAHodgeThetaObjectActual
end
