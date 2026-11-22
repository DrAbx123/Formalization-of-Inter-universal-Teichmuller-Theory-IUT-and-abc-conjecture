import tmp.sheaf.xif.paper.S2562CorrectedEssSurjLiftUniqueActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

/-! # S2630: cast helpers for the S2562 qside triangle -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual

namespace LeanFormal.IUT.XiFPaper.S2630CastHelpersActual

universe u

variable {F : Type u} [Field F]

/-- Transport a strong transformation along an equality of source pseudofunctors. -/

noncomputable def castStrongTrans
    {P Q R : EtaleStackPseudofunctor F} (h : P = Q)
    (L : Pseudofunctor.StrongTrans P R) :
    Pseudofunctor.StrongTrans Q R :=
  h ▸ L

@[simp] theorem castStrongTrans_rfl
    {P R : EtaleStackPseudofunctor F}
    (L : Pseudofunctor.StrongTrans P R) :
    castStrongTrans rfl L = L := rfl

theorem castStrongTrans_trans
    {P Q R : EtaleStackPseudofunctor F} {T : EtaleStackPseudofunctor F}
    (h : P = Q) (k : Q = R)
    (L : Pseudofunctor.StrongTrans P T) :
    castStrongTrans (h.trans k) L =
      castStrongTrans k (castStrongTrans h L) := by
  subst h; subst k; rfl

theorem castStrongTrans_vcomp
    {P Q R T : EtaleStackPseudofunctor F} (h : P = Q)
    (L : Pseudofunctor.StrongTrans P R)
    (M : Pseudofunctor.StrongTrans R T) :
    Pseudofunctor.StrongTrans.vcomp (castStrongTrans h L) M =
      castStrongTrans h (Pseudofunctor.StrongTrans.vcomp L M) := by
  subst h; rfl


section Type0

variable {F₀ : Type} [Field F₀]

/-- The 2-Yoneda comparison of the identity strong transformation is the
identity scheme morphism. -/
theorem homOfStrongTrans_id
    (S : SchemeOverField F₀) :
    S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.id
        (S1742YS (F := F₀) S)) = 𝟙 S := by
  rw [← S1742HomOfStrongTrans_def]
  rfl

/-- The 2-Yoneda comparison of a representable scheme map recovers the scheme
morphism. -/
theorem homOfSchemeRepresentableMap
    {S T : SchemeOverField F₀} (f : S ⟶ T)
    (M : SchemeRepresentableMap (F := F₀) f) :
    S1742HomOfStrongTrans M.transformation = f := by
  rw [← S1742HomOfStrongTrans_def]
  rw [M.app_eq]
  rfl

end Type0

#check homOfStrongTrans_id
#check homOfSchemeRepresentableMap
#print axioms homOfStrongTrans_id
#print axioms homOfSchemeRepresentableMap

#check castStrongTrans
#check castStrongTrans_trans
#check castStrongTrans_vcomp
#print axioms castStrongTrans_vcomp

end LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
end
