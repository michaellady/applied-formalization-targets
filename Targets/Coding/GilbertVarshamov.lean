import Applied.Coding.GilbertVarshamov
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.LiminfLimsup

/-!
# Open: is the binary Gilbert–Varshamov bound asymptotically tight?

- id: coding-gilbert-varshamov-tightness
- area: coding
- status: open
- source: E. N. Gilbert, Bell Syst. Tech. J. 31 (1952); R. R. Varshamov (1957); ProofAtlas Top 500 (Nov 2026), rank 138
- used-in: error-correcting codes for storage and communication; the benchmark every binary code family is compared with
- prerequisites: Hamming distance; counting
- statement-review: unreviewed

Informal statement. Let `A(n, d)` be the largest size of a binary code of length `n` and
minimum distance `d`. The Gilbert–Varshamov bound gives codes of rate at least `1 - H(δ)` at
relative distance `δ`, where `H` is the binary entropy. Whether one can do better
asymptotically for some `0 < δ < 1/2` is open; `GilbertVarshamovTight` says one cannot.

What is proved: the finite Gilbert–Varshamov bound, `A(n, d) · V(n, d - 1) ≥ 2ⁿ`, where
`V` is the size of a Hamming ball. Not yet proved: the entropy estimate of the ball size that
turns it into the rate statement.
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
