@echo off
cd /d D:\lean
echo START %DATE% %TIME%> "D:\lean\tmp\sheaf\xif\paper\S1413Run.log"
lake env lean tmp/sheaf/xif/paper/S1413SourceKPlaceQComparisonActual.lean >> "D:\lean\tmp\sheaf\xif\paper\S1413Run.log" 2>&1
set RC=%ERRORLEVEL%
>> "D:\lean\tmp\sheaf\xif\paper\S1413Run.log" echo EXIT=%RC%
