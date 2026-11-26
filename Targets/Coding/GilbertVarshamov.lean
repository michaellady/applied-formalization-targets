import Applied.Coding.GilbertVarshamov
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.LiminfLimsup

/-!
# Open: is the binary Gilbert–Varshamov bound asymptotically tight?

- id: coding-gilbert-varshamov-tightness
- area: coding
- status: open
- source: E. N. Gilbert, Bell Syst. Tech. J. 31 (1952); R. R. Varshamov (1957)
- used-in: error-correcting codes for storage and communication; the benchmark every binary code family is compared with
- prerequisites: Hamming distance; counting
- formalized-elsewhere: the open proposition `GilbertVarshamovTight` was not found stated in any project checked on 2026-11-25; tCSlib (github.com/Shilun-Allan-Li/tCSlib), `TCSlib/ErrorCorrectingCodes/MRRW.lean` :: `rate`, `codeA` defines the same rate `limsup log₂ A(n, ⌊δn⌋) / n`. The finite Gilbert–Varshamov bound is formalized in atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/Combinatorics/Coding/GilbertVarshamov.lean` :: `exists_code_pow_le_card_mul_sum` (`q`-ary) and cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Foundations/Data/Code/HammingBound.lean` :: `exists_le_minDist_and_prod_le_card_mul_card_filter_hammingDist_lt` (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. Let `A(n, d)` be the largest size of a binary code of length `n` and
minimum distance `d`. The Gilbert–Varshamov bound gives codes of rate at least `1 - H(δ)` at
relative distance `δ`, where `H` is the binary entropy. Whether one can do better
asymptotically for some `0 < δ < 1/2` is open; `GilbertVarshamovTight` says one cannot.

What is proved: the finite Gilbert–Varshamov bound, `A(n, d) · V(n, d - 1) ≥ 2ⁿ`, where
`V` is the size of a Hamming ball (alias below); its rate form (`coding-gilbert-varshamov-rate`);
Varshamov's linear version, a linear code of dimension at least `k` and minimum distance at
least `d` when `V(n - 1, d - 2) < 2ⁿ⁻ᵏ` (`coding-varshamov-linear`). On the upper side: the
Johnson bound in a ball (`coding-johnson-bound`) and the Elias–Bassalygo bound, finite and
asymptotic (`coding-elias-bassalygo`). Together (`coding-binary-rate-sandwich`,
`Targets.Coding.rate_sandwich`), for `0 < δ < 1/2`,
`1 - H(δ) ≤ lim inf log₂ A(n, ⌊δn⌋) / n ≤ lim sup log₂ A(n, ⌊δn⌋) / n ≤ 1 - H((1 - √(1 - 2δ)) / 2)`,
and the two outer bounds differ for every such `δ`. These are classical partial results; they
do not decide `GilbertVarshamovTight`. The Delsarte linear programming bound is formalized in
finite form with checked certificates (`coding-delsarte-lp`), but the best known asymptotic upper
bound derived from it (McEliece–Rodemich–Rumsey–Welch) is not formalized (here, or as far as we
found anywhere: tCSlib states it as `mrrw_bound` with `sorry`).
-/

open Finset Filter Applied.Coding

namespace Targets.Coding

alias gilbertVarshamov_bound := Applied.Coding.exists_code_card_mul_ballCard_ge

open Classical in
/-- The largest size of a binary code of length `n` and minimum distance at least `d`. -/
noncomputable def maxCodeSize (n d : ℕ) : ℕ :=
  ((univ : Finset (Finset (BWord n))).filter (IsCode d)).sup Finset.card

/-- Binary entropy in bits. -/
noncomputable def binaryEntropy (δ : ℝ) : ℝ :=
  -δ * Real.logb 2 δ - (1 - δ) * Real.logb 2 (1 - δ)

/-- **Open.** The best asymptotic rate of binary codes of relative distance `δ` equals the
Gilbert–Varshamov rate `1 - H(δ)` for every `0 < δ < 1/2`. -/
def GilbertVarshamovTight : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    limsup (fun n : ℕ => Real.logb 2 (maxCodeSize n ⌊δ * n⌋₊) / n) atTop
      = 1 - binaryEntropy δ

end Targets.Coding
