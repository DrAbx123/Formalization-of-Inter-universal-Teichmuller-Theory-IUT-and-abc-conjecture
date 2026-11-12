# S2450: empty-cover amalgamation attempt — subsingleton/EssSurj packaging incomplete

Date: 2026-11-02. Serialized lake env lean -j1.

Idea: empty presieve R = bottom at any S is a genuinely non-split family (no arrows); its index category is empty, and descent data for the empty family is expected to be a subsingleton. Then any object M of the fibre gives Amalgam with iso = eqToIso (Subsingleton.elim (toDescentData M) D).

ACTUAL so far:
- S2450_empty_category_isEmpty : IsEmpty (bottom : Presieve S).category, proof false x := x.property. Compiles.

INCOMPLETE:
- S2450_empty_descentData_subsingleton: after cases D1 D2, congr leaves dependent function/proof field equalities (obj, hom, pullHom_hom, hom_self, hom_comp) that need funext over the empty index and proof irrelevance; not closed.
- S2450_empty_effDescent: HasEffectiveDescentPresieve F bottom is Functor.EssSurj; my intro D shape was wrong; needs EssSurj constructor/packaging.

No empty-cover effective descent/Amalgam actual. No non-split Cech amalgamation actual.

Source SHA256 04321eab67ac5ba2f3dfe87f67dc3ca97ad26420c1e5b6b5f2aab33d3a8c9135; no olean. No IsStack claim, no fake.