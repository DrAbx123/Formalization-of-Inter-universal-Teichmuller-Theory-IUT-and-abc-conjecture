$root = 'D:\lean'
$status = Join-Path $root 'tmp\xif_watchdog_STATUS.md'
$log = Join-Path $root 'tmp\xif_parallel_build.log'
$res = Join-Path $root 'tmp\xif_parallel_results.log'
$lines = New-Object System.Collections.Generic.List[string]
$lines.Add('# xi-f central watchdog status')
$lines.Add('')
$lines.Add('time: ' + (Get-Date -Format 'yyyy-MM-dd HH:mm:ss'))
$all = Get-CimInstance Win32_Process
$py = $all | Where-Object { $_.Name -eq 'python.exe' -and $_.CommandLine -match 'xif_parallel_build' } | Select-Object -First 1
$desc = New-Object System.Collections.Generic.HashSet[int]
function Add-Desc([int]$id) {
  foreach ($c in $all | Where-Object { $_.ParentProcessId -eq $id }) {
    if ($desc.Add([int]$c.ProcessId)) { Add-Desc ([int]$c.ProcessId) }
  }
}
if ($py) {
  $lines.Add('central_build_pid: ' + $py.ProcessId)
  Add-Desc ([int]$py.ProcessId)
  $lines.Add('central_descendant_count: ' + $desc.Count)
} else { $lines.Add('central_build: NOT RUNNING') }
$centralLean = @()
$localLean = @()
foreach ($p in Get-CimInstance Win32_Process -Filter "Name='lean.exe'") {
  if ($desc.Contains([int]$p.ProcessId)) { $centralLean += $p } else { $localLean += $p }
}
$lines.Add('central_lean_workers: ' + $centralLean.Count)
foreach ($p in $centralLean) { $lines.Add('  central: pid=' + $p.ProcessId + ' ' + $p.CommandLine) }
$lines.Add('agent_local_lean: ' + $localLean.Count)
foreach ($p in $localLean) { $lines.Add('  LOCAL(should not run): pid=' + $p.ProcessId + ' ' + $p.CommandLine) }
if (Test-Path $log) { $lines.Add(''); $lines.Add('## log tail'); Get-Content $log -Tail 12 | ForEach-Object { $lines.Add($_) } }
if (Test-Path $res) { $r = Get-Content $res; $lines.Add(''); $lines.Add('## results'); $lines.Add('entries=' + ($r | Select-String '^PASS=').Count + ' ok=' + ($r | Select-String 'EXIT=0').Count + ' fail=' + ($r | Select-String 'EXIT=1').Count) }
$lines | Set-Content -LiteralPath $status -Encoding utf8
$lines | ForEach-Object { Write-Output $_ }
