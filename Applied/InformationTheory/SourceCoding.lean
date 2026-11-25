import Applied.InformationTheory.Gibbs
import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Shannon's lower bound on the expected length of a uniquely decodable code

A source code is a map `c : ι → List α` from source symbols to words over a finite alphabet
`α` with `D` letters. If `c` is injective and its set of codewords is uniquely decodable
(Mathlib's `InformationTheory.IsUniquelyDecodable`), then for every probability vector `p`
on `ι` the entropy of `p` is at most `log D` times the expected codeword length.

* `entropy_le_log_card_mul_expected_length`: `H(p) ≤ log D · ∑ p i · |c i|`, entropy in nats.
* `entropy_logb_le_expected_length`: for `D ≥ 2`, `H_D(p) ≤ ∑ p i · |c i|`, where
  `H_D(p) = -∑ p i log_D (p i)`; for `D = 2` this is the entropy in bits.

The proof combines the Kraft–McMillan inequality (in Mathlib) with Gibbs' inequality.
-/

open Finset Real InformationTheory

namespace Applied.InformationTheory

variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]

/-- Kraft–McMillan for an injective uniquely decodable source code, as a sum over source
symbols. -/
lemma sum_kraft_le_one (c : ι → List α) (hinj : Function.Injective c)
    (hud : IsUniquelyDecodable (Set.range c)) :
    ∑ i, (1 / (Fintype.card α : ℝ)) ^ (c i).length ≤ 1 := by
  classical
  have h := IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one
    (S := univ.image c) (by simpa using hud)
  rwa [Finset.sum_image fun a _ b _ hab => hinj hab] at h

/-- **Shannon's source coding lower bound** (noiseless coding theorem, converse part), in nats.
For an injective source code `c` with uniquely decodable set of codewords over an alphabet with
`D` letters, and any probability vector `p`, `H(p) ≤ log D · E[length]`. -/
theorem entropy_le_log_card_mul_expected_length (c : ι → List α) (hinj : Function.Injective c)
    (hud : IsUniquelyDecodable (Set.range c)) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    ∑ i, negMulLog (p i) ≤ log (Fintype.card α) * ∑ i, p i * (c i).length := by
  have hD : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hq : ∀ i, 0 < (1 / (Fintype.card α : ℝ)) ^ (c i).length := fun i => by positivity
  have h := sum_negMulLog_le_neg_sum_mul_log univ p
    (fun i => (1 / (Fintype.card α : ℝ)) ^ (c i).length) (fun i _ => hp i)
    (fun i _ => (hq i).le) (fun i _ h0 => absurd h0 (hq i).ne')
    (by rw [hsum]; exact sum_kraft_le_one c hinj hud)
  refine h.trans (le_of_eq ?_)
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [log_pow, one_div, log_inv]; ring

/-- **Shannon's source coding lower bound**, entropy to the base `D` of the code alphabet
(`D ≥ 2`): `-∑ p i log_D (p i) ≤ E[length]`. For a binary alphabet the left-hand side is the
entropy in bits. -/
theorem entropy_logb_le_expected_length (c : ι → List α) (hinj : Function.Injective c)
    (hud : IsUniquelyDecodable (Set.range c)) (hα : 2 ≤ Fintype.card α) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    -∑ i, p i * logb (Fintype.card α) (p i) ≤ ∑ i, p i * (c i).length := by
  have h := entropy_le_log_card_mul_expected_length c hinj hud p hp hsum
  have hlog : 0 < log (Fintype.card α : ℝ) := log_pos (by exact_mod_cast hα)
  have heq : -∑ i, p i * logb (Fintype.card α) (p i)
      = (∑ i, negMulLog (p i)) / log (Fintype.card α : ℝ) := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logb, negMulLog]; ring
  rw [heq, div_le_iff₀ hlog]
  linarith

end Applied.InformationTheory
