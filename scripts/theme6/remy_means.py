# 数値検証(3) の標本平均と標準誤差（paper_ja 第5節の脚注）。
# 使い方: gcc -O2 -o count_mnc theme6/count_mnc.c && python3 theme6/remy_means.py
# 種は 1..k の固定。所要 数分。
import subprocess, os, statistics as st
from fractions import Fraction as F
env=dict(os.environ,CSV='1')
for n,k in [(10**3,1000),(10**4,1000),(10**5,1000),(10**6,100),(10**7,20)]:
    am=[];an=[]
    for seed in range(1,k+1):
        out=subprocess.run([os.environ.get('COUNT_MNC','./count_mnc'),str(n),'rand',str(seed)],capture_output=True,text=True,env=env,check=True).stdout.strip().split(',')
        assert out[-1]=='OK'
        am.append(int(out[2])); an.append(int(out[3]))
    EM=F(n*(n-1),n+2)+2*n-1; EN=F(n*(n-1),n+2)+n+2+F((n-1)*(n-2),2*(2*n-1))
    def s(x): return st.mean(x), st.stdev(x)/len(x)**.5
    (mm,sm),(mn,sn)=s(am),s(an)
    print(f"n={n:>8} trees={k:>5}  A_M/n={mm/n:.6f}±{sm/n:.6f} (exact {float(EM)/n:.6f}, z={(mm-float(EM))/sm:+.2f})  A_N/n={mn/n:.6f}±{sn/n:.6f} (exact {float(EN)/n:.6f}, z={(mn-float(EN))/sn:+.2f})")
