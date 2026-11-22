# C3 consumer chain closure / audit record

Date: 2026-11-09 (Asia/Shanghai)
Toolchain: Lean 4.32.2 + Mathlib; builds via central watchdog (tmp/xif_guarded_queue.txt).

Scope: 22 files S2888-S2909, top consumer layer of normalized C3 IUT-II log-volume / comparison / Theta-q-pilot chain. All EXIT0, olean present.

## Axiom status

All 23 exported main theorems (S2897 exports two) depend only on:

[propext, Classical.choice, Quot.sound]

Verified by #print axioms in one probe importing all 22 modules: 23/23 trio; no sorryAx, no extra axioms.

## File / theorem table

| file | main theorem(s) | src size | src SHA-256 | olean size | olean SHA-256 |
|---|---|---|---|---|---|
| S2888C3LatticeRegionUnitScalingConsumer | C3LatticeRegion_unit_scaling_consumer | 4049 | 0F52C2153EB3CD2854ADB18093C082E5B9F2851333531A463CCA8C3D972F4717 | 65488 | C4A898CD0154711A9BFC294C8A1D1B06E5B7D753E9BEEAEAF6B0BE02ACCA0AAF |
| S2889C3ThetaQPilotScalingLatticeConsumer | C3ThetaQPilot_scaling_lattice_consumer | 3774 | F9313F28F5E782385B676F801393FB3DEDEC9C36C7F47638FEBB17FCCC9F0761 | 83624 | BA0A296D0CC39985F8A2CCFF37239D8F143551870AA07A226BA24B9F39DB24F8 |
| S2890C3LatticeLogVolumeScalingConsumer | C3Lattice_logVolume_scaling_consumer | 3243 | 0E697E72C6CD2D19121E8CC801596F07B2F228D5B5ABA67C84010069285BF1AC | 80792 | D18FED4AD6D0AFA92974F4433D0B53712BF742E4032D4F72CFE16F1DED940324 |
| S2891C3LatticeLogVolumeUnitConsumer | C3Lattice_logVolume_unit_consumer | 3204 | 707DE3728BCBA4A15B6EF55A3220BF315F34F5ACCFAB25B9C2635B8503710E31 | 63880 | 4B4B1F6A1E55B27C88904F6D6F2098758191621438067607BF579493EED8F1D2 |
| S2892C3LatticeRegionLogScalingCompareConsumer | C3LatticeRegion_logVolume_scaling_compare | 3388 | 70FDB450E2A3FD2F7348B77833499C8AFEBB95C707BF1A58B073B0533100942A | 68248 | D0946E7F9F54B389E26030AEE192175FCEF52FFD0C5BE621AACF8578CEBD96D8 |
| S2893C3LatticeRegionUnitLogVolumeCompareConsumer | C3LatticeRegion_unit_logVolume_compare | 3311 | 031CAE07E6A5FCC25CEDFEF305E5BF13163F64D70BF31000646645494BDA5A0B | 54344 | 0B2F05524A70837BBE021CBF4091E22FF2AF78159EBC3FD729C3B87474AD97BA |
| S2894C3ScalingLogVolumeAllConsumer | C3Scaling_logVolume_all_consumer | 4443 | F2ADE7F0880F740159875463E8E046E030701D75C3E33779F770CAB2B6DE5BE0 | 70448 | 8E563F68CE027198F001B8F2184903C52A3485E923DF76327C3ED54E13984691 |
| S2895C3ScalingLogVolumeOneConsumer | C3Scaling_logVolume_one_consumer | 3432 | 9D18367AFBD9E6B628AEA135E9EE5575789E8B41F645852E9406ADBF4901D8ED | 98704 | A1FD2BEABA8F8BEC3025C474CC8F37BEE7148E7BACB2DFAFCB6B0C23CFFCF674 |
| S2896C3ScalingLogVolumeSummaryConsumer | C3Scaling_logVolume_summary_consumer | 3963 | FAF89B11658B84776801286DC50E3081CF3E37FF340873FDE6D32964797FE96A | 88544 | EDCC3FBD74B6F98480F29F75E459784E619FC377F26BE3F6D3A91D5420CBF9C8 |
| S2897C3ThetaComparisonScalingConsumer | C3ThetaComparison_scaling_consumer / C3ThetaComparison_unit_scaling_consumer | 3741 | 4A92C30D20DC1DCC501AEB87600042C836B5420501BDBC8BB31B66CDD2323541 | 87144 | BA81DDB9193604534F47582319C805FE615191156A1AF6DD8864802DC2EA1415 |
| S2898C3ThetaComparisonScalingAllConsumer | C3ThetaComparison_scaling_all_consumer | 3581 | ABB83E347E690AC016BF20A1026863ABCD11F628B626662C8D45AD299F5C6DB9 | 68048 | 4C2E4C734D620B8EA4567AD4CF9ACA8FC5D1FF9F820939CC16D89529CE0EF695 |
| S2899C3ThetaComparisonUnitScalingAllConsumer | C3ThetaComparison_unit_scaling_all_consumer | 3402 | 51E9B30203AB2EEA2DCFB9F5A13E455910E5A1884C46067E93E8572724157E9F | 54136 | E5EA8D6012A9DD7B4A4A5A46BE5110A44FFFB706BB70F6F60EB8CFE33A226C06 |
| S2900C3ThetaComparisonScalingSummaryConsumer | C3ThetaComparison_scaling_summary_consumer | 3622 | 56F373ADCDB56B600AD13DFABEC229ED0750722DD1543639C7D969FF21D92167 | 73104 | 54FCE2AC4645CC78E165721510D8C0E14FD2B3CBEFEDA3BF28FD326FF5FFAA60 |
| S2901C3ThetaComparisonScaleOneConsumer | C3ThetaComparison_scale_one_consumer | 2874 | 961E28FD76DFCE1F0B92361D7BC47F7B6B3A731484E84144B1E5ADA70A37B4B1 | 92656 | A09BAA45C10EB70E77BA9154F0BB57CE2058F88276EC1A40055FE21A7BCB315D |
| S2902C3ThetaComparisonUnitQPilotConsumer | C3ThetaComparison_unit_scale_and_qPilot_consumer | 3227 | 41B14045BF638306B2B2BCAF45E4EEDFD0E4C82B442C57B1F29039FA699A771B | 58664 | 55B491790FC11B1AEA97B0AA41519DA91845E5B59D0BF57F4538F6381D760016 |
| S2903C3ThetaComparisonScalingLatticeConsumer | C3ThetaComparison_scaling_and_lattice_consumer | 3274 | 564530FA3D7C0090CE67A00B9240617036A3EE58FC77FBAD0BEB964335AE3520 | 70648 | 511675C923A28FBD95586C35683E8B79C6B4208A59B5A472DFAC5795F71809AF |
| S2904C3ThetaComparisonScalingFullSummaryConsumer | C3ThetaComparison_scaling_full_summary_consumer | 4483 | 5DEAC61BF8AD08E11936FF5471CD59DE5CDD34FAF63F622B129F3C8F48B6C1FB | 72240 | F5A38821C75A168F31E699187D3769645CBC75DAC799ADE765EF060A663507F1 |
| S2905C3ThetaComparisonScalingOneLatticeConsumer | C3ThetaComparison_scaling_one_and_lattice_consumer | 3521 | A49644CF3FF0DBF69DFE2CAF89213D604693454C68F35E42AE660A80469B85A2 | 46544 | 8C54B014ABB367283FEB0BD65DF7C86F81C1AE18944971E5D9852F83B1A87EE0 |
| S2906C3ThetaComparisonLogDataLinkConsumer | C3ThetaComparison_scaling_and_logData_consumer | 4057 | 1F7EC263834D48759D2A195F5C202EA25877B1BBFE8030D785FB607C23145F07 | 71864 | D810310FF9890EC5A9925F26135F3968FAB07E3D14FBD92B28093809BAADBFA8 |
| S2907C3ThetaComparisonLatticeLogVolumeConsumer | C3ThetaComparison_lattice_and_logVolume_consumer | 3587 | D63E65367E494ED85DB3E6FD24D147F956AE7E5BC8F1437C9BC3F8BD37471CB3 | 43976 | 9D388782EC123BCDF349B306A1476B1228464431AA34D50A976D1780A813625E |
| S2908C3ThetaComparisonFullLinkConsumer | C3ThetaComparison_full_link_consumer | 3893 | FEC7CBDCC63373D1A02FA66A588AA075432757944BD012415A9BD2D8D23ACFB5 | 68008 | CA22060890070EE866A3353CF31152866369CB820EAED1F8764E795EB17E6DD5 |
| S2909C3ThetaComparisonUnitLatticeConsumer | C3ThetaComparison_unit_and_lattice_consumer | 3240 | 06B53215A185AC680417BE0DB1B93EB4A5D52ADCA7B9454F4A3789D57C71F8AE | 59512 | A35729886E363BFF3B1DA85169C2A47C57EB437A7F0F9199414A3A844A42CA1D |

## Dependency skeleton

base actuals (selected):
  S2834/S2835 (Theta/q-pilot data)
  S2882/S2883 (real-log scaling and unit scaling)
  S2887/S2888 (lattice/region scaling and unit invariance)
consumer layer S2888..S2909:
  S2888 S2889 -> S2890 S2891 -> S2892 S2893 -> S2894 S2895 S2896
  S2897 -> S2898 S2899 -> S2900 S2901 S2902 S2903 S2905 S2908 S2909
  S2904 S2906 S2907 cross-link S2902/S2903/S2843/S2840

Semantics: every consumer is stated in image form ((fun x => g . x) '' S) rather than g . S, because Set-level SMul instances differ across modules; the image form is the transportable interface.

## Notes / closed issues

- S2888-S2909 originally used u . S / unitQHom w . S; cross-module Set SMul instance mismatch and tensor-lattice Pi-instance elaboration caused repeated failures. Resolution: image-form statements plus explicit (T) [Fintype] (e) binders where a lemma consumes region data; C3SetSmulGlobalActual remains only as legacy helper.
- S2890/S2891 needed unfold haarLogVolume before rewriting measure equalities.
- S2898/S2899 initially missed import/open S2897; fixed.
- S2901 needed image-form restatement of 1 . region.
- No further consumers should be added on this chain; it is a closed interface layer.

## Verification basis

- Source/olean hashes computed from the exact files above.
- Axiom probe: tmp/sheaf/xif/paper/_c3consumer_axioms.lean (imports all 22 modules, 23 #print axioms), output tmp/c3consumer_axioms.txt.
- No sorry, no axiom, no True/PUnit weakening in this layer.
