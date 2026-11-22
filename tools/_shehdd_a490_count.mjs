import { readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const wall=ROOT+'/tmp/sheaf/lana/iut/Iut/Wall';
const we=ROOT+'/tmp/sheaf/lana/iut/Iut/WallEquiv';
const n=f=>existsSync(f)?readdirSync(f).filter(x=>x.endsWith('.lean')).length:0;
console.log('Wall files='+n(wall)+' WallEquiv='+n(we));
console.log('Wall: '+readdirSync(wall).filter(x=>x.endsWith('.lean')).join(', '));
console.log('WallEquiv: '+readdirSync(we).filter(x=>x.endsWith('.lean')).join(', '));
