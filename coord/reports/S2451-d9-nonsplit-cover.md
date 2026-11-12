# S2451: non-identity fold cover presieve and canonical amalgam actual

Date: 2026-11-02. Serialized lake env lean -j1.

Using S2433NonidentityStrongRepresentable:
- S2451S := S2433T (affine base over Spec F').
- S2451Y := S1897CoverScheme S2433FoldCover (doubled affine fold cover).
- S2451Map := S1897CoverOver S2433FoldCover : S2451Y -> S2451S.
- S2451Presieve := Presieve.singleton S2451Map.
- S2451CanonicalDatum M := (S2029SheafPrestack K).toDescentData f |>.obj M.
- S2451CanonicalAmalgam M : Amalgam ... (S2451CanonicalDatum M), with M and Iso.refl.

EXIT=0, olean 23304, SHA256 e6136a4feac59ab0bdf92ae5d9784eca135c63fa0083c4c6740a5dd644f97e37, axioms propext/Classical.choice/Quot.sound.

Limits:
- The singleton presieve is built from the non-identity fold cover map S2433Map / S2433FoldCover.
- S2433G0_not_iso certifies the coproduct inclusion (not the projection S2451Map) is not iso.
- Proving S2451Presieve is in S2093EtalePrecoverage and the FULL S2445AmalgamationRequirement for arbitrary descent data is still missing. Only the canonical descent datum of an object is glued.

No general non-split Cech amalgamation, no IsStack claim, no fake.