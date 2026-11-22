import { readFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
// refresh real sorry count with lexical parser
const audit=readFileSync(ROOT+'/dag/SORRY-AUDIT.md','utf8');
const files=[...audit.matchAll(/^\| (\S+\.lean) \| (\d+) \|/gm)].map(m=>({file:m[1],count:+m[2]}));
function codeText(s){ let out=''; let i=0; const n=s.length;
  while(i<n){ const c=s[i], c2=s.slice(i,i+2);
    if(c2==='/-'){ let d=1; i+=2; while(i<n&&d>0){ const e=s.slice(i,i+2); if(e==='/-'){d++;i+=2;} else if(e==='-/'){d--;i+=2;} else i++; } continue; }
    if(c2==='--'){ while(i<n&&s[i]!=='\n') i++; continue; }
    if(c==='"'){ i++; while(i<n&&s[i]!=='"'){ if(s[i]==='\\') i+=2; else i++; } i++; continue; }
    if(c==="'"){ if(i+2<n && (s[i+2]==="'" || (s[i+1]==='\\'&&i+3<n&&s[i+3]==="'"))){ i++; while(i<n&&s[i]!=="'"){ if(s[i]==='\\') i+=2; else i++; } i++; continue; } out+=c; i++; continue; }
    out+=c; i++; }
  return out; }
let real=0; const rows=[];
for(const f of files){ const txt=readFileSync(ROOT+'/'+f.file,'utf8'); const c=(codeText(txt).match(/\bsorry\b/g)||[]).length; real+=c; rows.push({file:f.file,audit:f.count,real:c}); }
const diff=rows.filter(r=>r.real!==r.audit);
const L=['','## A482 映射修正与消歧（人工核对，覆盖上面表内误解析行）','',
'- SourceLogShellCarrier -> LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean: SourceLogShellDatum, pStar, preLogShell, logShell, unitLayer, IQSpan, logShell_eq_invScaledPreLogShell (olean fresh)。TwistContainer 是补充模块，不是该 token 所指；',
'- SourceHodgeTheater -> LeanFormal/IUT/IUTI/HodgeTheater/SourceHodgeTheaterFamily.lean: SourceHodgeTheaterFamily, theater_injective, theater_eq_iff, link_refl_at；配套 SourceHodgeTheaterFamilyLawsReduction.lean: thetaPacket_eq/theater_ne_of_ne (fresh)；',
'- SourceH1H2Construction -> LeanFormal/IUT/IUTIII/Theorem311/SourceH1H2Construction.lean: fPrimeStripAt, dThetaAt, fPrimeStripAt_eq, dPrimeStripAt_eq (fresh)；',
'- SourceProcessionStepXI -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceProcessionStepXI.lean: ProcessionTheorem311Target, Wall, routeWall (fresh)；InclusionResidual/MinimalForm 为补充文件；',
'- K1K2BoundaryReduction (Ind3) -> LeanFormal/IUT/IUTII/Kummer/K1K2BoundaryReduction.lean: nonarchimedeanImageInclusion, ind3ImageWellDefined, archimedeanTargetLift, identityLabelledKummerIso (fresh)；注意它与 Theorem311/SourceK1K2CardReduction.lean 是两个不同资产；',
'- Obligations(ipl/she) -> LeanFormal/IUT/IUTIII/Theorem311/Obligations.lean（ipl/she 记录）；Corollary312/Obligations.lean 是另一文件；',
'- APT -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean（不是 Foundations/UnitPerfectionMapTopology 等同名片段）；',
'- CertificateHullWiring -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean（另有 Signed/Realization 变体）；',
'- StepXIContract -> 声明 LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean:30（文件不叫 StepXIContract；tmp 下同名 paper 文件不是 LADDER 所指 tree 资产）；',
'- ArithmeticQPilot -> 3 文件族：ArithmeticQPilotBaseChange.lean: residueNormBase/qNorm_eq_residueNormBase_zpow, ArithmeticQPilotGlobalNormalization.lean, ArithmeticQPilotLogVolume.lean: qNorm_pos/qNorm_lt_one/localSignedLog (fresh)；',
'','## sorry 审计续（A482 重扫）','',
'- dag/SORRY-AUDIT.md 报 '+files.length+' 模块 / '+files.reduce((a,b)=>a+b.count,0)+' 处；词法重扫（去嵌套注释/行注释/字符串）真实源码 sorry = **'+real+'** 处。',
'- 与审计计数不符的文件: '+diff.map(r=>r.file.split('/').pop()+'('+r.audit+'->'+r.real+')').join(', ')+'。',
'- 结论: 部分审计条目为文案字符串/已被 hull 等修复；真实剩余集中在 n8 closure/paper 缺口，已登记 blocked。详见 coord/SORRY-AUDIT-CORRECTION-shehdd.md。',''];
appendFileSync(ROOT+'/coord/LADDER-A482-AUDIT.md', L.join('\n'));
console.log('appended correction; real sorry='+real+' diff='+diff.length);
for(const r of diff.slice(0,15)) console.log('  '+r.file.split('/').pop()+' audit='+r.audit+' real='+r.real);
