$root='D:\lean'
Set-Location $root
// drop legacy queue hints from plan (keep explicit extra-targets only)
$f='tools/dag_plan.mjs'
$c=Get-Content $f -Raw
$q="try{ for(const line of readFileSync(join(ROOT,'tmp','xif_guarded_queue.txt'),'utf8').split(/\r?\n/)){ const p=line.trim().replaceAll('\\\\','/'); if(p.endsWith('.lean')&&existsSync(join(ROOT,p))) extra.push(p); } }catch{}"
if($c.Contains($q)){ $c=$c.Replace($q,'') ; Write-Output 'queue-hint removed' } else { Write-Output 'queue-hint pattern not found' }
$c | Set-Content -NoNewline $f
// kill all watchdog instances
Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'dag_watchdog2' } | ForEach-Object { taskkill /F /PID $_.ProcessId 2>$null | Out-Null; Write-Output ('killed ' + $_.ProcessId) }
Start-Sleep -Seconds 2
// start single instances via node.exe with redirected logs
$node = (Get-Command node.exe).Source
Start-Process -FilePath $node -ArgumentList 'D:\lean\tools\dag_watchdog2.mjs' -WorkingDirectory $root -RedirectStandardOutput 'D:\lean\dag\watchdog\stdout.log' -RedirectStandardError 'D:\lean\dag\watchdog\stderr.log' -WindowStyle Hidden
Start-Sleep -Seconds 6
$inst = @(Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'dag_watchdog2' })
Write-Output ('instances=' + $inst.Count)
Get-Content dag\watchdog\watchdog.log -Tail 4