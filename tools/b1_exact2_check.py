import csv,math,statistics as st
rows=list(csv.DictReader(open('coord/b1_exact2_500_p60.csv')))
print('n',len(rows),'err',sum(1 for r in rows if 'error' in r))
pos=[r for r in rows if int(r['min_abs'])>0]
print('positive',len(pos),'zero',len(rows)-len(pos))
print('valid_div positive',sum(1 for r in pos if r['valid_div']=='True'),'/',len(pos))
print('valid_ge positive',sum(1 for r in pos if r['valid_ge']=='True'),'/',len(pos))
bad=[r for r in pos if r['valid_div']!='True']
print('bad',[(r['label'],r['min_abs'],r['r_f_opt']) for r in bad[:20]])
print('min/max min',min(int(r['min_abs']) for r in rows),max(int(r['min_abs']) for r in rows))
cs=[math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in pos]
print('Cobs max med mean',max(cs),st.median(cs),st.mean(cs))
for lo in range(0,500,100):
 a=[r for r in rows if lo<=int(r['N'])<lo+100]; z=[r for r in a if int(r['min_abs'])>0]
 cc=[math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in z]
 print('BIN',lo,len(a),'zero',len(a)-len(z),'pos',len(z),'max',max(cc) if cc else None,'med',st.median(cc) if cc else None,'maxmin',max([int(r['min_abs']) for r in z] or [0]))
