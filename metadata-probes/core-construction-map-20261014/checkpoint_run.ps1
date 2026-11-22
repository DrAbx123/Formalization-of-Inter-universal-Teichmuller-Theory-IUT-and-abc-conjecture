param(
  [string]$Db = 'D:/lean/logs/coordination/core-construction-map-20261014.sqlite'
)
$ErrorActionPreference = 'Stop'
$agent = 'dsh_original_input_owner'
$ctx = '{"run_id":"core-construction-map-20261014","protocol_version":"iut-agent-tree/2026-10-13-v1","contract_digest":"d4d54f29ce4d5ef081315ba738b9d3670535ed8f0c1239e2e859d6ebc2802056"}'
$inspect = '{"op":"inspect","actor_id":"' + $agent + '","generation":2,"agent_id":"' + $agent + '"}'
$dir = 'D:/lean/metadata-probes/core-construction-map-20261014'
$insPath = 'D:/lean/metadata-probes/core-construction-map-20261014/_inspect_tmp.json'
$cpPath  = 'D:/lean/metadata-probes/core-construction-map-20261014/_checkpoint_tmp.json'
$wtPath  = 'D:/lean/metadata-probes/core-construction-map-20261014/checkpoint_payload.json'

$summary = 'source_original_arithmetic_input-v1 checkpoint before WAITING_FEEDBACK on the exact unresolved source-defined interface request; no new source/probe work performed.'

$cpCheckpoint = '{"disclosure":"PROTOCOL_INCIDENT created unregistered artifacts under metadata-probes directory PUBLIC_CARD.md probe source_original_arithmetic_inputaudit.lean plus part2 to part9 and names checkpoint_payload.json checkpoint_v1_v2_v3.json inspect files bootstrap_input_v1.json checkpoint_run.ps1 and stateflow files; all created by me this session via write tool or WriteAllText with status created; PREWRITE existence check NOT performed so prior contents and overwrite risk are UNKNOWN; no deletes performed and no fresh checking now. Outside-whitelist access classes only names: directory enumerations of theorem311 dir D lean root iut dir lake build lib oleans; environment type queries of imported declarations SourceDefinition31Data InitialThetaArithmeticData SourceFaithfulBoundary Input DerivedPrerequisiteInput ThetaFieldTower clause records PuncturedEllipticCurve HodgeTheater FPrimeStrip concrete instances Theorem311Output ParametricTheorem311 DPrimeStripProcession; no contents of those sources read. Source hashes unchanged SourceOriginalInput 11C288D385682760B56890B24C57F1738A771DC6A75E2543EFFD67D9FFAFA795 InitialThetaInputCore 47DFC4FBF3A980381D580EE56342F6084C170EBB2C87671085DE1B06D1E60F1A SourceHodgeTheaterBridge DDACDA6560CEE45712A134F96585BB001B8B519745FB4291CEC602A5D6F366BE SourceProcessionBoundary 11185E318457E143AB24AFED854257F10D8347EF017DEB3932C15EB58B5A4442. Assembly sibling query UNRESOLVED from captured receipts: SourceTheorem311Realization.output never queried so kind signature producer unknown; captured R structure fields procession packet vertical evaluation genericFamily labelledCount labelledCount_pos and R.input DerivedPrerequisiteInput Label Choice; whether R.input.labelPrime tied to l UNRESOLVED; SourceH1H2Alignment and K2FrobenioidBoundary no captured evidence UNRESOLVED. Previous tuple-shaped forall l forall V existence proposal WITHDRAWN as source-frozen necessary theorem because tuple-shaped record existence is not source proof of paper hypotheses and may strengthen them."}'

$msg = 'Source-frozen interface request contract source_original_arithmetic_input-v1 digest d4d54f29ce4d5ef081315ba738b9d3670535ed8f0c1239e2e859d6ebc2802056. Please supply from the owner of LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary and the HodgeTheater family module the source-defined propositions behind SourceDefinition31Data arithmetic_reduction_compatibility arithmetic_torsion_compatibility arithmetic_orbicurve_compatibility arithmetic_section_compatibility arithmetic_cusp_compatibility and SourceOrbicurveClause curveCompatibility together with the actual source to paper linkage of place partition torsion module orbicurve sections cusp data to the elliptic curve and field tower and the family index equivalence construction. Acceptance requires source-defined hypotheses not an arbitrary forall l forall V existence theorem; the tuple-shaped forall l forall V record existence proposal is WITHDRAWN. Frozen consumer hashes SourceOriginalInput 11C288D385682760B56890B24C57F1738A771DC6A75E2543EFFD67D9FFAFA795 InitialThetaInputCore 47DFC4FBF3A980381D580EE56342F6084C170EBB2C87671085DE1B06D1E60F1A SourceHodgeTheaterBridge DDACDA6560CEE45712A134F96585BB001B8B519745FB4291CEC602A5D6F366BE SourceProcessionBoundary 11185E318457E143AB24AFED854257F10D8347EF017DEB3932C15EB58B5A4442.'

for ($i = 1; $i -le 8; $i++) {
  [System.IO.File]::WriteAllText($insPath, $inspect, (New-Object System.Text.UTF8Encoding($false)))
  $raw = Get-Content -Raw $insPath | python -X utf8 -B D:/lean/tools/agent_state.py --db $Db
  $obj = $raw | ConvertFrom-Json
  if ($obj.ok -ne $true) { Write-Output ('inspect_not_ok i=' + $i); Write-Output $raw; break }
  $state = $obj.result.agent.state
  $rev = $obj.revision
  Write-Output ('i=' + $i + ' rev=' + $rev + ' state=' + $state)
  if ($state -eq 'WAITING_FEEDBACK') {
    Write-Output 'ALREADY_WAITING no mutation attempted'
    Write-Output ($obj.result.agent.pending_feedback | ConvertTo-Json -Compress -Depth 6)
    break
  }

  $cp = '{"op":"checkpoint","request_id":"dsh_original_input_owner-cp-incident-v1","expected_revision":' + $rev + ',"actor_id":"' + $agent + '","generation":2,"agent_id":"' + $agent + '","context":' + $ctx + ',"checkpoint":' + $cpCheckpoint + ',"summary":"' + $summary + '"}'
  [System.IO.File]::WriteAllText($cpPath, $cp, (New-Object System.Text.UTF8Encoding($false)))
  $out = Get-Content -Raw $cpPath | python -X utf8 -B D:/lean/tools/agent_state.py --db $Db
  $code = $LASTEXITCODE
  Write-Output ('checkpoint exit=' + $code)
  Write-Output $out
  if ($code -ne 0) {
    if ($out -match 'REVISION_CONFLICT') { continue } else { break }
  }
  $obj2 = $out | ConvertFrom-Json
  $rev2 = $obj2.revision

  $wt = '{"op":"wait","request_id":"dsh_original_input_owner-wait-v1","expected_revision":' + $rev2 + ',"actor_id":"' + $agent + '","generation":2,"agent_id":"' + $agent + '","context":' + $ctx + ',"feedback_id":"dsh_original_input_owner-iface-srcdatav1-20261014","message":"' + $msg + '"}'
  [System.IO.File]::WriteAllText($wtPath, $wt, (New-Object System.Text.UTF8Encoding($false)))
  $out2 = Get-Content -Raw $wtPath | python -X utf8 -B D:/lean/tools/agent_state.py --db $Db
  $code2 = $LASTEXITCODE
  Write-Output ('wait exit=' + $code2)
  Write-Output $out2
  if ($code2 -eq 0 -or ($out2 -notmatch 'REVISION_CONFLICT')) { break }
}
