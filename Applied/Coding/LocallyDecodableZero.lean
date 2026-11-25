import Applied.Coding.LocallyDecodable

/-!
# Zero-query locally decodable codes do not exist

A decoder that reads no position of the word outputs a bit whose distribution does not depend
on the word. It cannot output both `0` on the codeword of a message with `x i = 0` and `1` on
the codeword of a message with `x i = 1` with probability above `1/2` each.

* `not_isLDC_zero`: for `k ≥ 1`, `δ ≥ 0` and `ε > 0` no code is a `(0, δ, ε)`-LDC.
-/

open Finset

namespace Applied.Coding

/-- **No zero-query locally decodable codes.** If `k ≥ 1`, `0 ≤ δ` and `0 < ε`, no code
`C : {0,1}ᵏ → {0,1}^ι` is a `(0, δ, ε)`-locally decodable code. -/
theorem not_isLDC_zero {ι : Type*} [Fintype ι] {k : ℕ} (hk : 0 < k)
    (C : (Fin k → Bool) → (ι → Bool)) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ¬ IsLDC C 0 δ ε := by
  rintro ⟨D, hD⟩
  set i : Fin k := ⟨0, hk⟩
  have h0 : ∀ x : Fin k → Bool, (hammingDist (C x) (C x) : ℝ) ≤ δ * Fintype.card ι := by
    intro x; simp only [hammingDist_self, Nat.cast_zero]; positivity
  have hf := hD (fun _ => false) i (C fun _ => false) (h0 _)
  have ht := hD (fun _ => true) i (C fun _ => true) (h0 _)
  have hans : ∀ (y : ι → Bool) ω, (fun j => y (D.query i ω j)) = (Fin.elim0 : Fin 0 → Bool) :=
    fun _ _ => funext fun j => j.elim0
  simp only [LocalDecoder.successProb, hans] at hf ht
  have hsum : (∑ ω, if D.out i ω Fin.elim0 = false then D.prob ω else 0)
      + (∑ ω, if D.out i ω Fin.elim0 = true then D.prob ω else 0) = 1 := by
    rw [← Finset.sum_add_distrib, ← D.prob_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    cases D.out i ω Fin.elim0 <;> simp
  linarith

end Applied.Coding
