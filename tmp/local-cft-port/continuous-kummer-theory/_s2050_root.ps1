$root='D:\lean\tmp\local-cft-port\continuous-kummer-theory'
$env:LEAN_PATH=$root
Set-Location 'D:\lean'
$src=Join-Path $root 'ContinuousKummerTheory.lean'
$out=Join-Path $root 'ContinuousKummerTheory.olean'
$lo=Join-Path $root '_s2050_logs\ContinuousKummerTheory.out.log'
$le=Join-Path $root '_s2050_logs\ContinuousKummerTheory.log'
$sw=[System.Diagnostics.Stopwatch]::StartNew()
$p=Start-Process -FilePath 'lake.exe' -ArgumentList @('env','lean','-R',$root,'-o',$out,$src) -NoNewWindow -PassThru -RedirectStandardOutput $lo -RedirectStandardError $le
$done=$p.WaitForExit(240000)
$sw.Stop()
if($done){ $c=$p.ExitCode } else { try{$p.Kill($true)}catch{}; $c=-999 }
Add-Content -Path $lo -Value ('EXIT=' + $c + ' SECONDS=' + [math]::Round($sw.Elapsed.TotalSeconds,1))
Write-Output ('ROOT_EXIT=' + $c + ' secs=' + [math]::Round($sw.Elapsed.TotalSeconds,1))