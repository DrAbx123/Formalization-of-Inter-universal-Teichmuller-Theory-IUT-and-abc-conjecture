# LIT-CHAIN-INVENTORY — literal reading chain and iv→lit bridge (A1029)

Status: read-only source inventory; no compile.

## 1. Core definitions/signatures

`Iut/Concrete/ThetaRegion.lean`:
- `litLabels (i) : Set (Lab n i) := Set.univ` (:241);
- `ivLabels (i) := {distinguished n i}` (:237);
- `rhsDataOn (S : ∀ i : Fin ((D.ℓ-1)/2), Set (Lab ((D.ℓ-1)/2) i))
    (hS : ∀ i, (S i).Nonempty) : RHSData D` (:320-331):
  fields `container := LocalTheory.container D.placeSect n`,
  `vol := LocalTheory.vol D.placeSect n`,
  `hull := LocalTheory.hull D.placeSect n`,
  `thetaPilot := D.thetaPilotOn n S hS`,
  `thetaPilot_hullAdmissible := thetaComponentOn_admissible`;
- `rhsData : RHSData D := rhsDataOn (ivLabels _) (ivLabels_nonempty _)` (:335-336);
- `rhsDataLit : RHSData D := rhsDataOn (litLabels _) (litLabels_nonempty _)` (:340-341);
  **there is no separate `rhsDataLitOn`** — lit is the generic `rhsDataOn litLabels`;
- `concreteVariantData : Corollary312VariantData := { data := D, qPilot := D.qPilot,
    rhsData := D.rhsData }` (:359-362);
- `concreteVariantDataLit := { data := D, qPilot := D.qPilot, rhsData := D.rhsDataLit }`
  (:367-370);
- `Cor312VariantHolds : Prop := ∀ D, Corollary312Variant (concreteVariantData D)` (:375-376);
- `Cor312LiteralHolds : Prop := ∀ D, Corollary312Variant (concreteVariantDataLit D)`
  (:383-384).

`Iut/Concrete/Literal.lean`:
- `InitialThetaData.rhs_le_rhsLit : D.rhsData.rhs ≤ D.rhsDataLit.rhs` (:84) —
  literal RHS dominates iv RHS;
- `cor312Literal_of_variant (h : Cor312VariantHolds) : Cor312LiteralHolds` (:115-116) —
  iv ⇒ literal, via `rhs_le_rhsLit`.

## 2. Dependencies of `rhsDataLit` / `concreteVariantDataLit`

To build `D.rhsDataLit` for a concrete `D : InitialThetaData` one needs:
1. `D : InitialThetaData` (with `F, Fbar, E, VBad, global, prime, orb, localData`);
2. `LocalTheory.container D.placeSect n` (`n = (ℓ-1)/2`);
3. `LocalTheory.vol D.placeSect n : LogVolumeData container`;
4. `LocalTheory.hull D.placeSect n : ContainerHullSystem container`;
5. `D.thetaPilotOn n litLabels litLabels_nonempty`, i.e.:
   - `D.thetaComponentOn n i litLabels vQ c` (defined from `scaleElt`,
     `LocalTheory.shell`, `indAut`; `ThetaRegion` definitions),
   - `D.thetaComponentOn_admissible` for every tuple,
6. `D.qPilot : QPilotData D` (badFinset, weights, `logQ`),
7. the hull admissibility/compactness fields consumed by `RHSData`
   (`thetaPilot_hullAdmissible`, etc.).

These are **lana `InitialThetaData`/`LocalTheory` objects, not our
`SourcePilotRegionDataL`**.  Our S1487 concrete input is an `OriginalInput`
(`S1487FaithfulInput`), with C3 L record and SourceImageRealization data; it
does not carry `LocalTheory.container/vol/hull` or `thetaComponentOn`.

## 3. Can our S3137L/Mzk1 outputs connect to lit?

- Our A989/A994 outputs:
  - `C3L : SourcePilotRegionDataL`;
  - `R : ∀ v, SourceImageRealization v`;
  - `thetaHullVolumeAtL`/`globalThetaHullLogVolumeL` (source-set-volume model).
- `concreteVariantDataLit.rhs` is
  `(D.rhsDataLit).rhs = (LocalTheory.vol ...).processionVol (hull of thetaPilotOn litLabels)`.
  It needs an `InitialThetaData D` and lana `LocalTheory` Haar/hull data;
  none of these is present in the S1487 L chain.
- A bridge would need at least:
  1. an `InitialThetaData D` whose underlying arithmetic matches S1487's
     concrete Gaussian arithmetic;
  2. identification of its `LocalTheory.container/vol/hull` with the L carrier's
     tensor data (or a new L-version `RHSData`);
  3. equality/inequality `rhsDataLit.rhs = -R` (or `≤`) for our R;
  4. for the literal hull, the lit label union and `min_l ord_p(q_{v_l})`
     behavior (not the iv single label).
  These are all **missing**; no direct connection currently exists.

## 4. TG dependencies

- `Iut/Concrete/Literal.lean` imports `Iut.Concrete.LocalEstimate`, which
  imports `Iut.Concrete.SectionAverage`; no `TemperedFundamentalGroups` import
  in the literal chain itself.
- The lit chain's blockers are the **missing lana `Concrete`/`LocalTheory`
  oleans and the `InitialThetaData` construction**, not TG.
- TG appears only in the Wall/Foundations layers above; it is not imported by
  `ThetaRegion`/`Literal`/`LocalEstimate`.

## 5. Inventory summary

| item | status |
|---|---|
| `concreteVariantDataLit` | DEFINED (ThetaRegion:367-370), uses `D.rhsDataLit` |
| `rhsDataLit` | DEFINED (`rhsDataOn litLabels`), no separate `rhsDataLitOn` |
| `rhs_le_rhsLit` | PROVED in lana (Literal:84) |
| `cor312Literal_of_variant` | PROVED in lana (Literal:115) |
| our S1487/L outputs → lit variant | GAP: no `InitialThetaData`, no `LocalTheory`/RHSData bridge |
| TG in lit chain | none directly; blockers are missing lana oleans/InitialThetaData |
