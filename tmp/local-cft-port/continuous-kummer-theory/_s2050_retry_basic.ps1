$root='D:\lean\tmp\local-cft-port\continuous-kummer-theory'
$env:LEAN_PATH=$root
Set-Location 'D:\lean'
$log = Join-Path $root '_s2050_logs'
foreach ($m in @('ContinuousKummerTheory.ContH1.Basic')) {
  $rel = ($m -replace '\.','\') + '.lean'
  $src = Join-Path $root $rel
  $out = Join-Path $root (($m -replace '\.','\') + '.olean')
  if (Test-Path $out) { Remove-Item $out -Force }
  $sw=[System.Diagnostics.Stopwatch]::StartNew()
  $cmdline = 'lake env lean -R "' + $root + '" -o "' + $out + '" "' + $src + '" 2>&1'
  $output = & cmd /c $cmdline
  $code = $LASTEXITCODE
  $sw.Stop()
  $output | Out-File -FilePath (Join-Path $log 'retry-ContH1.Basic.log') -Encoding utf8
  Write-Output ('RETRY ' + $m + ' code=' + $code + ' secs=' + [math]::Round($sw.Elapsed.TotalSeconds,1))
}
Write-Output 'RETRY_DONE'