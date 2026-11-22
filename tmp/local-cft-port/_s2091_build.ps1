
$ErrorActionPreference = 'Continue'
$plan = Get-Content 'D:\lean\tmp\local-cft-port\_s2091_plan.json' -Raw | ConvertFrom-Json
$order = $plan.order
$deps = $plan.deps
$fileOf = $plan.fileOf
$OUT = 'D:\lean\tmp\local-cft-port\oleans2091'
$PORT = 'D:\lean\tmp\local-cft-port\local-class-field-theory-main'
$CKT = 'D:\lean\tmp\local-cft-port\continuous-kummer-theory-main'
$log = 'D:\lean\tmp\local-cft-port\_s2091_build.tsv'
$raw = 'D:\lean\tmp\local-cft-port\_s2091_build.raw.log'
$TAB = [char]9
$env:LEAN_PATH = @(
  'D:\lean\.lake\packages\Cli\.lake\build\lib\lean',
  'D:\lean\.lake\packages\batteries\.lake\build\lib\lean',
  'D:\lean\.lake\packages\Qq\.lake\build\lib\lean',
  'D:\lean\.lake\packages\aesop\.lake\build\lib\lean',
  'D:\lean\.lake\packages\proofwidgets\.lake\build\lib\lean',
  'D:\lean\.lake\packages\importGraph\.lake\build\lib\lean',
  'D:\lean\.lake\packages\LeanSearchClient\.lake\build\lib\lean',
  'D:\lean\.lake\packages\plausible\.lake\build\lib\lean',
  'D:\lean\.lake\packages\mathlib\.lake\build\lib\lean',
  'D:\lean\.lake\build\lib\lean',
  $OUT
) -join ';'
$lean = (Get-Command lean).Source
$done = @{}; $fail = @{}
foreach ($m in $order) {
  $out = Join-Path $OUT (($m -replace '\.','\') + '.olean')
  if (Test-Path $out) { $done[$m] = $true }
}
(('PLAN ' + (Get-Date -Format o) + ' total=' + $order.Count + ' prebuilt=' + $done.Count)) | Set-Content $raw
$THROTTLE = 6
while ($true) {
  $pending = @($order | Where-Object { -not $done.ContainsKey($_) -and -not $fail.ContainsKey($_) })
  if ($pending.Count -eq 0) { break }
  $ready = @()
  foreach ($m in $pending) {
    $ok = $true
    foreach ($d in $deps.$m) { if (-not $done.ContainsKey($d)) { $ok = $false; break } }
    if ($ok) { $ready += $m }
  }
  if ($ready.Count -eq 0) {
    foreach ($m in $pending) { $fail[$m] = 'BLOCKED' }
    break
  }
  $batch = @($ready | Select-Object -First $THROTTLE)
  $jobs = @(); $names = @()
  foreach ($m in $batch) {
    $src = $fileOf.$m
    $root = if ($src -like ($CKT + '*')) { $CKT } else { $PORT }
    $out = Join-Path $OUT (($m -replace '\.','\') + '.olean')
    New-Item -ItemType Directory -Force -Path (Split-Path $out) | Out-Null
    $jobs += Start-Job -ScriptBlock {
      param($lean, $src, $out, $root)
      $sw = [Diagnostics.Stopwatch]::StartNew()
      $o = & $lean --root $root -o $out $src 2>&1 | Out-String
      $sw.Stop()
      [pscustomobject]@{ Exit = $LASTEXITCODE; Sec = [math]::Round($sw.Elapsed.TotalSeconds,1); Out = $o }
    } -ArgumentList $lean, $src, $out, $root
    $names += $m
  }
  $jobs | Wait-Job | Out-Null
  for ($i = 0; $i -lt $jobs.Count; $i++) {
    $r = Receive-Job $jobs[$i]; Remove-Job $jobs[$i]
    $m = $names[$i]
    $srcHash = (Get-FileHash $fileOf.$m -Algorithm SHA256).Hash
    if ($r.Exit -eq 0) {
      $done[$m] = $true
      $out = Join-Path $OUT (($m -replace '\.','\') + '.olean')
      $b = if (Test-Path $out) { (Get-Item $out).Length } else { -1 }
      $oh = if (Test-Path $out) { (Get-FileHash $out -Algorithm SHA256).Hash } else { 'NONE' }
      (@($m,'EXIT=0',("SEC=" + $r.Sec),("OLEAN_BYTES=" + $b),("OLEAN_SHA256=" + $oh),("SRC_SHA256=" + $srcHash)) -join $TAB) | Add-Content $log
    } else {
      $fail[$m] = 'FAIL'
      (@($m,'EXIT=FAIL',("SEC=" + $r.Sec),("SRC_SHA256=" + $srcHash)) -join $TAB) | Add-Content $log
      (('----- OUTPUT ' + $m + ' -----' + [char]10 + $r.Out)) | Add-Content $raw
    }
  }
  (('ROUND ' + (Get-Date -Format o) + ' done=' + $done.Count + ' fail=' + $fail.Count)) | Add-Content $raw
}
(('ALLDONE ' + (Get-Date -Format o) + ' done=' + $done.Count + ' fail=' + $fail.Count)) | Add-Content $raw
foreach ($k in $fail.Keys) { (('FAILED: ' + $k + ' ' + $fail[$k])) | Add-Content $raw }
