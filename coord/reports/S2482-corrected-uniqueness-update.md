# Corrected uniqueness updated to TwoIso; classification still missing

## Updated corrected interface (EXIT=0)
SourceSignQuotientDataCorrected now has:
  unique_elliptic_involution :
    forall inv, TwoIso (comp inv inv) id -> inv != Hom.id ->
      Nonempty (TwoIso inv ellipticInvolution).
No equality of Hom is required.

S2482CorrectedEllipticUniqueness (audit file) uses the same TwoIso form.

## Actual files
- S2482CorrectedSourceSignQuotientActual.lean: source SHA 53E074A7397EF4069E68B279F65F74D9C10AD6C393D7A2A2967247997EDA9ED6, olean SHA 828901E39579E138BAC3E6B3995139BFF80912616BE6B21A8417451230307285, EXIT=0.
- S2482InvolutionUniquenessAuditActual.lean: source SHA D339C8C2B11D2DADEA94F15FFF49E46B49DCA0C935446D3A8FDD81D41BEECDD8, olean SHA FB83D0AFC5A7AAAC11A062D6AE43571BF379B7CCD2A9EB936FAABAE0CFD89EFE, EXIT=0.
- S2482QiNontrivialActual.lean: nontriviality/refutation actual (SHA 380587FF..., olean 645F6D3A...).

## Still missing: S2482OrderTwoAlgAutClassification
  forall phi : R ~= R, phi^2=id -> phi=id or phi=S2482CoordinateRingInvolution.
No inhabitant. Proof plan: Spec fully faithful; phi F-algebra automorphism; phi fixes x;
phi(y)=±y; nonidentity excludes +y. The classification step is not formalized.

Once classification is actual, the TwoIso form of corrected uniqueness still needs the 2-Yoneda
comparison from algebra/scheme equality to a TwoIso of strong transformations.

## Remaining geometry unchanged
signAction diagram/atBase/generator_identification; cF quotient/witness; xF/cF groups;
xK/cK/scalar extensions; epsilon. Place fields actual via S2490PlaceFieldsA.