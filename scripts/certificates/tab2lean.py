import pickle,sys
from tabgen import H,R,D,IMAX
tailLo,tailHi,phiLo,phiHi=pickle.load(open("table.pkl","rb"))
LEAF=32
def entry(i): return f"⟨{tailLo[i]}, {tailHi[i]}, {phiLo[i]}, {phiHi[i]}⟩"
def tree(lo,hi,leaf,ind):
    # indices lo..hi-1
    if hi-lo==1: return " "*ind+leaf(lo)
    mid=(lo+hi)//2
    return (" "*ind+f"bif Nat.blt i {mid if leaf is entry else mid*LEAF} then\n"+tree(lo,mid,leaf,ind+1)+"\n"+" "*ind+"else\n"+tree(mid,hi,leaf,ind+1))
nleaf=(IMAX+1+LEAF-1)//LEAF
out=[]
out.append('''import Applied.Statistics.NormalTable

/-!
# Table of the standard normal distribution function on the grid `i / 1024`, `0 ≤ i ≤ 10752`

Generated data (integer arithmetic only, see the header of `Applied.Statistics.NormalTable` for
the recursion): for each grid point lower and upper bounds, scaled by `10^40`, for the upper
tail `1 - Φ(i / 1024)` and the density. `tab_ok` checks the table in the kernel with
`decide +kernel`; `tab_valid` is the resulting correctness statement. Nothing in this file is
trusted: a wrong digit makes `tab_ok` fail.
-/

namespace Applied.Statistics.NormalTableData

open Applied.Statistics.NormalTable

set_option maxRecDepth 100000
set_option linter.unusedVariables false
''')
for k in range(nleaf):
    lo=k*LEAF; hi=min(lo+LEAF,IMAX+1)
    out.append(f"/-- Table entries {lo} to {hi-1}. -/\ndef leaf{k} (i : ℕ) : Entry :=\n"+tree(lo,hi,entry,2)+"\n")
out.append("/-- The table. -/\ndef tab (i : ℕ) : Entry :=\n"+tree(0,nleaf,lambda k:f"leaf{k} i",2)+"\n")
out.append(f'''/-- Last index of the table. -/
def imax : ℕ := {IMAX}

theorem tab_ok : tableOK tab imax = true := by decide +kernel

theorem imax_le : imax ≤ H * H := by decide

/-- Every entry of the table is correct. -/
theorem tab_valid : ∀ i ≤ imax, (tab i).Valid i := valid_of_tableOK tab_ok

end Applied.Statistics.NormalTableData
''')
open(sys.argv[1],"w").write("\n".join(out))
