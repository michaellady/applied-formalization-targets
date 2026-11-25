import Applied.Coding.LocallyDecodable
import Applied.Coding.LinearTwoQueryLDC

/-!
# The matching form gives locally decodable codes

This file connects the combinatorial matching form `IsLinearTwoQueryLDC` of
`Applied/Coding/LinearTwoQueryLDC.lean` with the library's probabilistic definition `IsLDC`
(`Applied/Coding/LocallyDecodable.lean`), in one direction.

* `linearCode a`: the binary linear code `x ↦ (⟨a j, x⟩ mod 2)_j` of the vectors `a j ∈ 𝔽₂ᵏ`.
* `IsLinearTwoQueryLDC.isLDC`: if `a` is a linear two-query LDC in matching form with
  parameter `δ > 0` and `m ≥ 1`, then `linearCode a` is a `(2, τ, 1/2 - τ/δ)`-LDC for every `τ`.
  The decoder picks a uniformly random pair `(u, v)` of a sub-matching of `Mᵢ` of size
  `⌈δ m⌉`, reads `y_u, y_v` and outputs their sum; a corruption of at most `τ m` positions
  spoils at most `τ m` pairs.

The converse direction (a linear code with a two-query decoder has large matchings, the first
step of Goldreich–Karloff–Schulman–Trevisan) is NOT formalized, so the exponential lower bound
`IsLinearTwoQueryLDC.four_rpow_le` is not proved for `IsLDC`.
-/

open Finset

namespace Applied.Coding

/-- The binary linear code of the vectors `a j ∈ 𝔽₂ᵏ`: the codeword of `x` lists the inner
products `⟨a j, x⟩ mod 2`. -/
def linearCode {k m : ℕ} (a : Fin m → Fin k → ZMod 2) (x : Fin k → Bool) (j : Fin m) : Bool :=
  decide (∑ l, a j l * (if x l then (1 : ZMod 2) else 0) = 1)

/-- On the uncorrupted codeword, a pair `(u, v)` with `a u + a v = eᵢ` recovers `x i`. -/
lemma linearCode_xor {k m : ℕ} (a : Fin m → Fin k → ZMod 2) (x : Fin k → Bool) {u v : Fin m}
    {i : Fin k} (h : a u + a v = Pi.single i 1) :
    xor (linearCode a x u) (linearCode a x v) = x i := by
  unfold linearCode
  have hs : (∑ l, a u l * (if x l then (1 : ZMod 2) else 0)) +
      (∑ l, a v l * (if x l then (1 : ZMod 2) else 0)) = if x i then 1 else 0 := by
    rw [← sum_add_distrib]
    simp_rw [← add_mul]
    have : ∀ l, a u l + a v l = (Pi.single i 1 : Fin k → ZMod 2) l := fun l => by
      rw [← Pi.add_apply, h]
    simp_rw [this, Pi.single_apply]
    rw [Finset.sum_eq_single i (fun l _ hl => by simp [hl]) (by simp)]
    simp
  generalize (∑ l, a u l * (if x l then (1 : ZMod 2) else 0)) = s at hs
  generalize (∑ l, a v l * (if x l then (1 : ZMod 2) else 0)) = r at hs
  cases hx : x i <;> rw [hx] at hs <;> revert s r <;> decide

/-- **Matching-form linear two-query LDCs are locally decodable codes.** If `0 < δ`, `0 < m` and
`a` is a linear two-query LDC in matching form with parameter `δ`, then `linearCode a` is a
`(2, τ, 1/2 - τ/δ)`-locally decodable code, for every `τ`. -/
theorem IsLinearTwoQueryLDC.isLDC {k m : ℕ} {a : Fin m → Fin k → ZMod 2} {δ : ℝ}
    (h : IsLinearTwoQueryLDC a δ) (hδ : 0 < δ) (hm : 0 < m) (τ : ℝ) :
    IsLDC (linearCode a) 2 τ (1 / 2 - τ / δ) := by
  classical
  set t : ℕ := ⌈δ * m⌉₊ with ht
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htge : δ * m ≤ t := Nat.le_ceil _
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (mul_pos hδ hmR) htge
  -- sub-matchings of size exactly `t`
  have hsub : ∀ i : Fin k, ∃ M : Finset (Fin m × Fin m), IsPairMatching M ∧
      (∀ e ∈ M, a e.1 + a e.2 = Pi.single i 1) ∧ M.card = t := by
    intro i
    obtain ⟨M, hM, hsum, hcard⟩ := h i
    obtain ⟨M', hM', hc'⟩ := exists_subset_card_eq (Nat.ceil_le.mpr hcard)
    exact ⟨M', fun e he e' he' hne => hM e (hM' he) e' (hM' he') hne,
      fun e he => hsum e (hM' he), hc'⟩
  choose M hM hsum hcard using hsub
  let σ : (i : Fin k) → Fin t → Fin m × Fin m := fun i ω =>
    ((M i).equivFin.symm (Fin.cast (hcard i).symm ω)).1
  have hσmem : ∀ i ω, σ i ω ∈ M i := fun i ω => ((M i).equivFin.symm _).2
  have hσinj : ∀ i, Function.Injective (σ i) := by
    intro i ω ω' hω
    have := (M i).equivFin.symm.injective (Subtype.ext hω)
    exact Fin.cast_injective _ this
  let D : LocalDecoder (Fin m) k 2 :=
    { Ω := Fin t
      prob := fun _ => 1 / t
      prob_nonneg := fun _ => by positivity
      prob_sum := by simp [htpos.ne']
      query := fun i ω j => if j = 0 then (σ i ω).1 else (σ i ω).2
      out := fun _ _ b => xor (b 0) (b 1) }
  refine ⟨D, fun x i y hy => ?_⟩
  -- the corrupted positions
  set B : Finset (Fin m) := univ.filter fun j => y j ≠ linearCode a x j with hB
  have hBcard : (B.card : ℝ) ≤ τ * m := by
    have : B.card = hammingDist y (linearCode a x) := rfl
    rw [this]; simpa using hy
  -- the outcomes on which the decoder errs
  set bad : Finset (Fin t) :=
    univ.filter fun ω => ¬ xor (y (σ i ω).1) (y (σ i ω).2) = x i with hbad
  have hbadB : bad.card ≤ B.card := by
    refine card_le_card_of_injOn
      (fun ω => if (σ i ω).1 ∈ B then (σ i ω).1 else (σ i ω).2) ?_ ?_
    · intro ω hω
      simp only [hbad, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hω
      simp only
      split_ifs with h1
      · exact h1
      · by_contra h2
        apply hω
        have e1 : y (σ i ω).1 = linearCode a x (σ i ω).1 := by
          by_contra hne; exact h1 (mem_filter.mpr ⟨mem_univ _, hne⟩)
        have e2 : y (σ i ω).2 = linearCode a x (σ i ω).2 := by
          by_contra hne; exact h2 (mem_filter.mpr ⟨mem_univ _, hne⟩)
        rw [e1, e2]
        exact linearCode_xor a x (hsum i _ (hσmem i ω))
    · intro ω _ ω' _ hωω
      by_contra hne
      have hne' : σ i ω ≠ σ i ω' := fun h => hne (hσinj i h)
      obtain ⟨h1, h2, h3, h4⟩ := hM i _ (hσmem i ω) _ (hσmem i ω') hne'
      simp only at hωω
      split_ifs at hωω <;> simp_all
  have hsucc : D.successProb y i (x i) = ((t : ℝ) - bad.card) / t := by
    have hgood : (univ.filter fun ω : Fin t => xor (y (σ i ω).1) (y (σ i ω).2) = x i).card
        + bad.card = t := by
      rw [hbad, Finset.card_filter_add_card_filter_not]; simp
    have hgood' : ((univ.filter fun ω : Fin t =>
        xor (y (σ i ω).1) (y (σ i ω).2) = x i).card : ℝ) = t - bad.card := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast hgood
    rw [← hgood']
    change (∑ ω : Fin t, if xor (y (σ i ω).1) (y (σ i ω).2) = x i then (1 / t : ℝ) else 0) = _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsucc, le_div_iff₀ htpos]
  have hbadR : (bad.card : ℝ) ≤ τ * m := le_trans (by exact_mod_cast hbadB) hBcard
  have hτ : 0 ≤ τ := by
    have : (0 : ℝ) ≤ τ * m := le_trans (Nat.cast_nonneg _) hBcard
    exact nonneg_of_mul_nonneg_left this hmR
  -- `τ m ≤ (τ / δ) t` because `δ m ≤ t`
  have hkey : τ * m ≤ τ / δ * t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    nlinarith [mul_le_mul_of_nonneg_left htge hτ]
  nlinarith

end Applied.Coding
