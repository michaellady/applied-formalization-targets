import pickle,sys
from certgen import BLOCKS, D
w=int(sys.argv[1]); out=pickle.load(open(f"cert_{w}.pkl","rb")); path=sys.argv[2]; ETAexp=int(sys.argv[3])
CH=int(sys.argv[4]) if len(sys.argv)>4 else 32
chunks=[out[i:i+CH] for i in range(0,len(out),CH)]
L=[]
L.append('''import Applied.Statistics.BlockCertificate
import Applied.Statistics.NormalTableData

/-!
# Certificate data for Dobriban's three-block model at level `1/100`

The model of E. Dobriban, arXiv:2607.12208 (2026), equations (1)–(3): per replication, `96` true
nulls `(3/10) Z + (√91/10) ε`, `1` non-null `12/5 - (3/10) Z + (√91/10) η` and `3` non-nulls
`22/5 - (18/25) Z + (√301/25) ξ`.

`bins` (split into chunks `bins0`, `bins1`, …) lists, for each bin `(zl/1024, zh/1024]` of the factor axis, the cut-offs (in units
`1/1024`) of the cells that bracket the Benjamini–Hochberg threshold from above, and the
cut-off of the lower bracket. The data were produced by an untrusted search; the theorems `chunk*_ok` check
them in the kernel (`decide +kernel`) with the integer checker of
`Applied.Statistics.BlockCertificate` and the table of `Applied.Statistics.NormalTableData`.
The bins and cut-offs differ from those of the preprint's Appendix B (grid `1/1024` instead of
`1/100` and `1/1000`, cells of variable length, bins of width `'''+str(w)+'''/1024`).
-/

namespace Applied.MultipleTesting.DobribanCert

open Applied.Statistics.NormalTable Applied.Statistics.NormalTableData
open Applied.MultipleTesting.BlockCert

set_option maxRecDepth 100000
''')
names=["null block: `96` statistics `(3/10) Z + (√91/10) ε`","first non-null block: `1` statistic `12/5 - (3/10) Z + (√91/10) η`","second non-null block: `3` statistics `22/5 - (18/25) Z + (√301/25) ξ`"]
for g,blk in enumerate(BLOCKS):
    mult,tn,td,bn,bd,rl,rh=blk
    L.append(f"/-- The {names[g]}. -/\ndef block{g} : BlockQ := ⟨{mult}, {tn}, {td}, {bn}, {bd}, {rl}, {rh}⟩\n")
L.append('''/-- The three blocks. -/
def blk (g : Fin 3) : BlockQ := if g.val = 0 then block0 else if g.val = 1 then block1 else block2

/-- The level is `1 / αinv = 1/100`. -/
def αinv : ℕ := 100

/-- The Chebyshev slack is `η = ETA / (D * 100) = 10^(''' + str(ETAexp-42) + ''')`. -/
def ETA : ℕ := 10 ^ '''+str(ETAexp)+'''
''')
for ci,ch in enumerate(chunks):
    L.append(f"/-- Bins {ci*CH} to {ci*CH+len(ch)-1}. -/\ndef bins{ci} : List Bin := [")
    rows=[]
    for (zl,zh,cs,b,term) in ch:
        rows.append(f"  ⟨{zl}, {zh}, [{', '.join(map(str,cs))}], {b}⟩")
    L.append(",\n".join(rows)+"]\n")
    S=sum(t[4] for t in ch)
    L.append(f"/-- Sum of the terms of `bins{ci}` (scaled by `10^40`). -/\ndef sum{ci} : ℕ := {S}\n")
    L.append(f"theorem chunk{ci}_ok : chunkOK tab imax blk αinv ETA bins{ci} sum{ci} = true := by\n  decide +kernel\n")
n=len(chunks)
L.append("/-- The chunks of bins. -/\ndef chunks : List (List Bin) :=\n  ["+", ".join(f"bins{i}" for i in range(n))+"]\n")
L.append("/-- The chunk sums. -/\ndef sums : List ℕ :=\n  ["+", ".join(f"sum{i}" for i in range(n))+"]\n")
L.append("/-- All bins. -/\ndef bins : List Bin := chunks.flatten\n")
fa="List.Forall₂.nil"
for i in range(n-1,-1,-1):
    fa=f"(List.Forall₂.cons chunk{i}_ok\n    {fa})"
L.append("""theorem params_ok : paramsOK blk αinv ETA = true := by decide +kernel

theorem sorted_ok : sortedOK chunks.flatten = true := by decide +kernel

theorem sum_ok : D < sums.sum := by decide +kernel

/-- The chunk sums add up to more than `1.04 * 10^40`. -/
theorem sum_gt : 104 * D < 100 * sums.sum := by decide +kernel

/-- Every chunk passes its check. -/
theorem chunks_ok :
    List.Forall₂ (fun l S => chunkOK tab imax blk αinv ETA l S = true) chunks sums :=
  """+fa+"""

/-- The chunk sums are lower bounds for the sum of all bin terms. -/
theorem sum_le : sums.sum ≤ (bins.map (binTerm tab imax blk ETA)).sum :=
  (chunks_key chunks sums chunks_ok).2

/-- The certificate passes the check. -/
theorem cert_ok : certOK tab imax blk αinv ETA bins = true :=
  certOK_of_chunks params_ok chunks sums chunks_ok sorted_ok sum_ok

end Applied.MultipleTesting.DobribanCert
""")
open(path,"w").write("\n".join(L))
