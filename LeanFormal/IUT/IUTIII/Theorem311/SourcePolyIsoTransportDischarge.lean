import LeanFormal.IUT.IUTIII.Theorem311.SourcePolyIsoTransportLaws
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Card-IPL discharge assessment: canonical kernel-level discharge and the O3 route algebra

Companion module to `SourcePolyIsoTransportLaws.lean` (SHA256
`E064E76534E9542A6F66D0E077D01B0C7ADCB3F2ECFBDA8D1726FC9035EAEE53`).  That
module froze the Card-IPL conditional assembly path with the supply
`CardIPLTransportSupply` (O1--O4) as hypotheses; this module is the discharge
assessment of those hypotheses and closes the part that is independent of
the source-level chain.

## Closures here

* Non-vacuity of the frozen obligation list: every shell carries the
  canonical supply `trivialSupply` (identity poly-isomorphism, empty
  algorithm route, integer times-mu carrier with trivial action, identity
  Kummer-evaluation factor).  Consequently the exchange-shape interface is
  realized on every shell (`trivialSupply_exchangeShape`), the transported
  relation collapses to the shell relation
  (`trivialSupply_polyIsoRel_eq_rel`), and the relation is inhabited on the
  identity link (`reflShell_trivialSupply_rel_self`), so the conditional
  laws of the companion module are never degenerate on these grounds.  This
  is a canonical kernel-level discharge witness only: it is NOT a source
  instantiation.
* The reduced O3 field (`provenance`, `polyIso_eq_provenance`) is equivalent
  to a single group element: route folds act as the (Ind1)-translations
  `act1 s` with `s = route.sum` (`routeApply_eq_act1_sum`), route
  composition and inversion are closed (`routeApply_append`,
  `routeApply_inv_cancel`), and the field is checkable in sum form
  (`routeApply_eq_iff_act1_sum`).  The relation-level route form reads back
  through the `act1`-translated second leg (`routeRel_iff_act1_sum`).

## Open source-level discharge (named cards; coordination report, section t2.6)

* O3 source discharge: the "induced by operations in the algorithm" clause
  of Remark 3.11.1, (iii).  The times-mu prime-strip module records this
  clause as not formalized, and that module is in flight; no type-level
  bridge from its records to the kernel shell is built here.
* O2 source discharge: the full poly-isomorphism object of the source
  times-mu layer (the API-4 data face) together with the adjacent-column
  comparison square (API-2, in flight) and a bridge from the source record
  layer to `L.mid ≃ L.mid`.  None of these modules is imported here.

## Non-claims

No construction of prime strips, of times-mu carriers, or of full
poly-isomorphisms; no claim that the canonical witness reflects source
data; no strengthening or weakening of the frozen obligation list; the two
negative results of the G1 verdict remain relied-on history and are not
re-proved.
-/

namespace LeanFormal.IUT

namespace Theorem311Source

namespace PolyIsoTransport

open LeanFormal.IUT.MultiradialKernel

universe u v w z

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-! ## 1. The route algebra of the reduced O3 reduction -/

namespace LinkSpan

variable {core1 core2 : Core Label Choice}

/-- Cancellation in the application orientation of the link carrier's
(Ind1)-action: applying `act1 (-g)` after `act1 g` returns the starting
state.  This is the shell-level companion of the kernel-level
`ind1_inv_cancel`. -/
theorem act1_inv_cancel (L : LinkSpan core1 core2) (g : Label) (m : L.mid) :
    L.act1 (-g) (L.act1 g m) = m := by
  have h := L.act1_add g (-g) m
  rw [add_neg_cancel, L.act1_zero] at h
  exact h.symm

end LinkSpan

/-- The empty route acts as the identity on the link carrier. -/
theorem routeApply_nil {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (m : L.mid) : routeApply L [] m = m := by
  unfold routeApply
  rw [List.foldl_nil]

/-- The reduced route fold is the single (Ind1)-translation by the sum of
its steps: `act1_add` telescopes the fold.  This is the closed form of the
reduced O3 reduction. -/
theorem routeApply_eq_act1_sum {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (route : List Label) (m : L.mid) :
    routeApply L route m = L.act1 route.sum m := by
  induction route generalizing m with
  | nil =>
    rw [routeApply_nil, List.sum_nil]
    exact (L.act1_zero m).symm
  | cons g t ih =>
    calc routeApply L (g :: t) m
        = routeApply L t (L.act1 g m) := by
            unfold routeApply
            rw [List.foldl_cons]
      _ = L.act1 t.sum (L.act1 g m) := ih (L.act1 g m)
      _ = L.act1 (g + t.sum) m := (L.act1_add g t.sum m).symm
      _ = L.act1 ((g :: t).sum) m := by rw [List.sum_cons]

/-- Route composition: the fold over `r₁ ++ r₂` is the fold over `r₂` after
the fold over `r₁`. -/
theorem routeApply_append {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (r₁ r₂ : List Label) (m : L.mid) :
    routeApply L (r₁ ++ r₂) m = routeApply L r₂ (routeApply L r₁ m) := by
  rw [routeApply_eq_act1_sum L (r₁ ++ r₂) m, routeApply_eq_act1_sum L r₁ m,
    routeApply_eq_act1_sum L r₂ (L.act1 r₁.sum m), List.sum_append]
  exact L.act1_add r₁.sum r₂.sum m

/-- A singleton route is the single (Ind1)-translation by its step. -/
theorem routeApply_singleton {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (g : Label) (m : L.mid) : routeApply L [g] m = L.act1 g m := by
  unfold routeApply
  rw [List.foldl_cons, List.foldl_nil]

/-- The singleton route by the negated sum inverts a route fold. -/
theorem routeApply_inv_cancel {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (route : List Label) (m : L.mid) :
    routeApply L [-(route.sum)] (routeApply L route m) = m := by
  rw [routeApply_eq_act1_sum L route m, routeApply_singleton]
  exact LinkSpan.act1_inv_cancel L route.sum m

/-- Discharge criterion for the reduced O3 field: an equivalence equals a
route fold if and only if it equals the single (Ind1)-translation by the
route's sum. -/
theorem routeApply_eq_iff_act1_sum {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (φ : L.mid ≃ L.mid) (route : List Label) :
    (∀ m, φ m = routeApply L route m) ↔ (∀ m, φ m = L.act1 route.sum m) := by
  constructor
  · intro h m
    rw [h m, routeApply_eq_act1_sum]
  · intro h m
    rw [h m, ← routeApply_eq_act1_sum]

/-- Relation-level closed form of the route form: the second leg reads back
as the (Ind1)-translation by the provenance sum. -/
theorem routeRel_iff_act1_sum {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (E : CardIPLTransportSupply L) (a b : Choice) :
    routeRel L E a b ↔
      ∃ m : L.mid, L.left m = a ∧ L.right (L.act1 E.provenance.sum m) = b := by
  simp only [routeRel, routeApply_eq_act1_sum]

/-! ## 2. The canonical supply (kernel-level discharge witness) -/

/-- The canonical supply carried by every shell: identity poly-isomorphism,
empty algorithm route, the integer times-mu carrier with trivial action, and
the identity Kummer-evaluation factor.  Every O1--O4 field is discharged at
this canonical point, which makes the companion module's conditional laws
non-degenerate on every shell.  This is NOT a source instantiation: it
carries no source data, its times-mu carrier is not the source times-mu
layer, and it does not resolve the open source-level discharge. -/
def trivialSupply {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2) :
    CardIPLTransportSupply L where
  XMu := ℤ
  xmuGroup := inferInstance
  xmuAct := fun _ x => x
  xmuAct_zero := fun _ => rfl
  xmuAct_add := fun _ _ _ => rfl
  polyIso := Equiv.refl L.mid
  polyIso_act1 := fun _ _ => rfl
  polyIso_act2 := fun _ _ => rfl
  provenance := []
  polyIso_eq_provenance := fun m => (routeApply_nil L m).symm
  kummerEval :=
    { lower := id
      upper := id
      kummer := id
      lower_left := fun _ => rfl
      upper_right := fun _ => rfl }

/-- The canonical supply's poly-isomorphism is the identity. -/
theorem trivialSupply_polyIso {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2) :
    (trivialSupply L).polyIso = Equiv.refl L.mid := rfl

/-- The canonical supply's algorithm route is empty. -/
theorem trivialSupply_provenance {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2) :
    (trivialSupply L).provenance = [] := rfl

/-- At the canonical supply the transported relation collapses to the shell
relation, so the companion module's transfer laws restrict to the shell's
two-route laws. -/
theorem trivialSupply_polyIsoRel_eq_rel {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) (a b : Choice) :
    polyIsoRel L (trivialSupply L) a b ↔ L.Rel a b :=
  polyIsoRel_eq_rel_of_polyIso_refl L (trivialSupply L) (trivialSupply_polyIso L) a b

/-- Nonemptiness of the transported relation at the canonical supply on the
identity link: the exchange laws are not vacuous over an empty relation. -/
theorem reflShell_trivialSupply_rel_self (core : Core Label Choice) (a : Choice) :
    polyIsoRel (LinkSpan.refl core) (trivialSupply (LinkSpan.refl core)) a a :=
  ⟨a, rfl, rfl⟩

/-- The exchange-shape consumer interface is realized on every shell via the
canonical supply. -/
theorem trivialSupply_exchangeShape {core1 core2 : Core Label Choice}
    (L : LinkSpan core1 core2) :
    CardIPLExchangeShape L (trivialSupply L) :=
  cardIPLExchangeShape L (trivialSupply L)

end PolyIsoTransport

end Theorem311Source

namespace Audit

/-- The Card-IPL discharge assessment at the reduced kernel level: the
canonical supply witnesses non-vacuity of the O1--O4 obligation list on
every shell, with the transported relation collapsing to the shell
relation, and the reduced O3 field is characterized by the route fold's
closed form; source-level discharge (API-1/API-2/N12) remains open. -/
def cardIPLTransportCanonicalDischarge : Obligation :=
  { id := "IUT-III.card-ipl-transport-canonical-discharge"
    source :=
      "IUT III, Remark 3.11.1, (iii) (IPL) and (iv) (APT, HIS); " ++
        "Corollary 3.12, proof, Steps (xi-b) and (xi-c)"
    status := VerificationStatus.provedKernel
    note :=
      "Kernel-level discharge assessment of the supply obligations left " ++
        "open by `IUT-III.card-ipl-poly-iso-transport-laws`: the canonical " ++
        "supply `trivialSupply` witnesses non-vacuity of the O1--O4 " ++
        "obligation list on every shell, the transported relation collapses " ++
        "to the shell relation, and the exchange-shape interface is " ++
        "realized; the reduced O3 field is characterized by the route " ++
        "fold `routeApply_eq_act1_sum` (routes act as act1-translations by " ++
        "the step sum, closed under composition and inversion).  " ++
        "Source-level discharge of O2/O3 (API-1, API-2, and the N12 " ++
        "induced-by clause) remains open; named cards in the coordination " ++
        "report, section t2.6."
    dependsOn := [ "IUT-III.card-ipl-poly-iso-transport-laws" ] }

end Audit

end LeanFormal.IUT
