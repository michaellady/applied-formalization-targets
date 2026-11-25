import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Linear two-query locally decodable codes need exponential length

A binary linear code of length `m` for `k`-bit messages is given by `m` vectors
`a₀, …, a_{m-1} ∈ 𝔽₂ᵏ`: the codeword of `x` lists the inner products `⟨a_j, x⟩`. In the
*matching form* of a linear two-query locally decodable code with parameter `δ`, for every
message index `i` there is a matching `Mᵢ` of at least `δ m` pairs of codeword positions such
that `a_u + a_v = eᵢ` for every pair `(u, v) ∈ Mᵢ`. (Reading `y_u` and `y_v` and adding them then
recovers `xᵢ` from the uncorrupted codeword; a corruption of `τ m` positions spoils at most
`τ m` pairs of the matching.)

We prove that such a code has length `m ≥ 4 ^ (δ k)` (`IsLinearTwoQueryLDC.four_rpow_le`).
This is an exponential lower bound of the type proved by Goldreich, Karloff, Schulman and
Trevisan (2002). The proof here goes through the edge-isoperimetric inequality of the
hypercube, in a weighted form:

* `cubeEdgeWeight w`: for a weight `w : 𝔽₂ᵏ → ℕ`, the sum over all ordered hypercube edges
  `(p, p + eᵢ)` of `min (w p) (w (p + eᵢ))`.
* `cubeEdgeWeight_mul_log_two_le`: `cubeEdgeWeight w · log 2 ≤ W log W` where `W = ∑ₚ w p`
  (for `w` the indicator of a set `A`, this is the edge-isoperimetric inequality
  `2 |E(A)| ≤ |A| log₂ |A|`).
* `two_mul_card_le_sum_min`: a matching whose pairs all have difference `v ≠ 0` has at most
  `½ ∑ₚ min (w p) (w (p + v))` pairs, where `w p` is the number of positions `j` with `a_j = p`.
-/

open Finset Real

namespace Applied.Coding

/-! ### A real inequality -/

private lemma mul_log_mul_left' {s x : ℝ} (hs : s ≠ 0) :
    (s * x) * log (s * x) = s * x * log s + s * (x * log x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [log_mul hs hx]; ring

/-- For `0 ≤ b ≤ a`: `a log a + b log b + 2 b log 2 ≤ (a + b) log (a + b)`. -/
lemma add_mul_log_le_of_le {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    a * log a + b * log b + 2 * b * log 2 ≤ (a + b) * log (a + b) := by
  rcases eq_or_lt_of_le (show 0 ≤ a + b by linarith) with hs | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0; simp
  set s := a + b with hsdef
  set p := b / s with hpdef
  have hp0 : 0 ≤ p := div_nonneg hb hs.le
  have hp1 : p ≤ 2⁻¹ := by rw [hpdef, div_le_iff₀ hs]; linarith
  have hbE : 2 * p * log 2 ≤ binEntropy p := by
    have h := strictConcave_binEntropy.concaveOn.2 (show (0 : ℝ) ∈ Set.Icc 0 1 from
      ⟨le_refl 0, zero_le_one⟩) (show (2⁻¹ : ℝ) ∈ Set.Icc 0 1 from ⟨by norm_num, by norm_num⟩)
      (show 0 ≤ 1 - 2 * p by linarith) (show 0 ≤ 2 * p by linarith)
      (show 1 - 2 * p + 2 * p = 1 by ring)
    have e : (1 - 2 * p) • (0 : ℝ) + (2 * p) • (2⁻¹ : ℝ) = p := by
      simp only [smul_eq_mul]; ring
    rw [e] at h
    simpa [smul_eq_mul] using h
  have hb' : b = s * p := by rw [hpdef]; field_simp
  have ha' : a = s * (1 - p) := by
    have : a = s - b := by rw [hsdef]; ring
    rw [this, hb']; ring
  have hent : binEntropy p = -(p * log p) - (1 - p) * log (1 - p) := by
    rw [binEntropy, log_inv, log_inv]; ring
  have key : a * log a + b * log b = s * log s - s * binEntropy p := by
    rw [hent]
    conv_lhs => rw [ha', hb', mul_log_mul_left' hs.ne', mul_log_mul_left' hs.ne']
    ring
  have hmul : s * (2 * p * log 2) ≤ s * binEntropy p := mul_le_mul_of_nonneg_left hbE hs.le
  have h2 : 2 * b * log 2 = s * (2 * p * log 2) := by rw [hb']; ring
  rw [key, h2]
  linarith

/-- For `a, b ≥ 0`: `a log a + b log b + 2 min(a, b) log 2 ≤ (a + b) log (a + b)`. -/
lemma add_mul_log_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * log a + b * log b + 2 * min a b * log 2 ≤ (a + b) * log (a + b) := by
  rcases le_total b a with h | h
  · rw [min_eq_right h]; exact add_mul_log_le_of_le hb h
  · rw [min_eq_left h, add_comm a b]
    have := add_mul_log_le_of_le ha h
    linarith

private lemma natCast_mul_log_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by exact_mod_cast hn))

/-! ### The weighted edge-isoperimetric inequality on the hypercube -/

/-- For a weight `w` on the hypercube `𝔽₂ᵏ`, the sum over all ordered edges `(p, p + eᵢ)` of
`min (w p) (w (p + eᵢ))`. -/
def cubeEdgeWeight {k : ℕ} (w : (Fin k → ZMod 2) → ℕ) : ℕ :=
  ∑ i : Fin k, ∑ p, min (w p) (w (p + Pi.single i 1))

private lemma sum_zmod_two {M : Type*} [AddCommMonoid M] (g : ZMod 2 → M) :
    ∑ b, g b = g 0 + g 1 := Fin.sum_univ_two g

private lemma sum_cube_succ {k : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (k + 1) → ZMod 2) → M) :
    ∑ p, f p = ∑ q, f (Fin.cons 0 q) + ∑ q, f (Fin.cons 1 q) := by
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => ZMod 2).sum_comp, Fintype.sum_prod_type,
    sum_zmod_two]
  rfl

private lemma cons_add_single_zero {k : ℕ} (b : ZMod 2) (q : Fin k → ZMod 2) :
    (Fin.cons b q : Fin (k + 1) → ZMod 2) + Pi.single 0 1 = Fin.cons (b + 1) q := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.succ_ne_zero]

private lemma cons_add_single_succ {k : ℕ} (b : ZMod 2) (q : Fin k → ZMod 2) (i : Fin k) :
    (Fin.cons b q : Fin (k + 1) → ZMod 2) + Pi.single i.succ 1 =
      Fin.cons b (q + Pi.single i 1) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [(Fin.succ_ne_zero i).symm]
  · simp [Pi.single_apply]

private lemma cubeEdgeWeight_succ {k : ℕ} (w : (Fin (k + 1) → ZMod 2) → ℕ) :
    cubeEdgeWeight w = 2 * ∑ q, min (w (Fin.cons 0 q)) (w (Fin.cons 1 q))
      + cubeEdgeWeight (fun q => w (Fin.cons 0 q))
      + cubeEdgeWeight (fun q => w (Fin.cons 1 q)) := by
  unfold cubeEdgeWeight
  rw [Fin.sum_univ_succ, sum_cube_succ]
  simp only [cons_add_single_zero, cons_add_single_succ, sum_cube_succ (k := k)]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [zero_add, h11, Finset.sum_add_distrib]
  simp only [min_comm (w (Fin.cons 1 _)) (w (Fin.cons 0 _))]
  ring

/-- **Weighted edge-isoperimetric inequality.** For every weight `w : 𝔽₂ᵏ → ℕ` of total mass
`W`, `cubeEdgeWeight w · log 2 ≤ W log W`. -/
theorem cubeEdgeWeight_mul_log_two_le {k : ℕ} (w : (Fin k → ZMod 2) → ℕ) :
    (cubeEdgeWeight w : ℝ) * log 2 ≤ ((∑ p, w p : ℕ) : ℝ) * log ((∑ p, w p : ℕ) : ℝ) := by
  induction k with
  | zero => simpa [cubeEdgeWeight] using natCast_mul_log_nonneg _
  | succ k ih =>
    set w0 : (Fin k → ZMod 2) → ℕ := fun q => w (Fin.cons 0 q)
    set w1 : (Fin k → ZMod 2) → ℕ := fun q => w (Fin.cons 1 q)
    have hW : ∑ p, w p = ∑ q, w0 q + ∑ q, w1 q := sum_cube_succ w
    have hmin : ∑ q, min (w0 q) (w1 q) ≤ min (∑ q, w0 q) (∑ q, w1 q) :=
      le_min (sum_le_sum fun q _ => min_le_left _ _) (sum_le_sum fun q _ => min_le_right _ _)
    have hminR : ((∑ q, min (w0 q) (w1 q) : ℕ) : ℝ) ≤
        min ((∑ q, w0 q : ℕ) : ℝ) ((∑ q, w1 q : ℕ) : ℝ) := by
      rw [← Nat.cast_min]; exact_mod_cast hmin
    have h0 := ih w0
    have h1 := ih w1
    have hlog := add_mul_log_le (Nat.cast_nonneg (∑ q, w0 q)) (Nat.cast_nonneg (∑ q, w1 q))
    have hl2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
    rw [cubeEdgeWeight_succ, hW]
    push_cast
    push_cast at hminR h0 h1 hlog
    nlinarith [mul_le_mul_of_nonneg_right hminR hl2]

/-! ### Matchings -/

/-- `M` is a matching on the positions `Fin m`: distinct pairs of `M` share no endpoint. (The
pairs are ordered; `(u, v)` and `(v, u)` cannot both lie in `M`.) -/
def IsPairMatching {m : ℕ} (M : Finset (Fin m × Fin m)) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2

/-- The number of positions `j` with `a j = p`. -/
def fiberCount {k m : ℕ} (a : Fin m → Fin k → ZMod 2) (p : Fin k → ZMod 2) : ℕ :=
  (univ.filter fun j => a j = p).card

lemma sum_fiberCount {k m : ℕ} (a : Fin m → Fin k → ZMod 2) : ∑ p, fiberCount a p = m := by
  unfold fiberCount
  rw [← card_eq_sum_card_fiberwise (fun j _ => mem_univ (a j))]
  simp

private lemma add_self_zmod_two {k : ℕ} (v : Fin k → ZMod 2) : v + v = 0 := by
  funext l
  have : ∀ x : ZMod 2, x + x = 0 := by decide
  exact this (v l)

/-- A matching whose pairs `(u, v)` all satisfy `a u + a v = v₀` with `v₀ ≠ 0` has at most
`½ ∑ₚ min (w p) (w (p + v₀))` pairs, where `w = fiberCount a`. -/
theorem two_mul_card_le_sum_min {k m : ℕ} (a : Fin m → Fin k → ZMod 2)
    {M : Finset (Fin m × Fin m)} (hM : IsPairMatching M) {v : Fin k → ZMod 2} (hv : v ≠ 0)
    (hsum : ∀ e ∈ M, a e.1 + a e.2 = v) :
    2 * M.card ≤ ∑ p, min (fiberCount a p) (fiberCount a (p + v)) := by
  classical
  set N : (Fin k → ZMod 2) → ℕ := fun p => (M.filter fun e => a e.1 = p ∨ a e.2 = p).card
    with hN
  have hvv := add_self_zmod_two v
  -- `N p ≤ w p`
  have hNle : ∀ p, N p ≤ fiberCount a p := by
    intro p
    refine card_le_card_of_injOn (fun e => if a e.1 = p then e.1 else e.2) ?_ ?_
    · intro e he
      simp only [coe_filter, Set.mem_ofPred_eq] at he
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      split_ifs with h
      · exact h
      · exact he.2.resolve_left h
    · intro e he e' he' hee
      simp only [coe_filter, Set.mem_ofPred_eq] at he he'
      by_contra hne
      obtain ⟨h1, h2, h3, h4⟩ := hM e he.1 e' he'.1 hne
      simp only at hee
      split_ifs at hee <;> simp_all
  -- `N (p + v) = N p`
  have hNeq : ∀ p, N (p + v) = N p := by
    intro p
    simp only [hN]
    congr 1
    refine filter_congr fun e he => ?_
    have h := hsum e he
    have h2 : a e.2 = v + a e.1 := by
      calc a e.2 = (a e.1 + a e.1) + a e.2 := by rw [add_self_zmod_two, zero_add]
        _ = a e.1 + (a e.1 + a e.2) := by abel
        _ = v + a e.1 := by rw [h, add_comm]
    rw [h2]
    have i1 : v + a e.1 = p + v ↔ a e.1 = p := by rw [add_comm p v]; exact add_right_inj v
    have i2 : a e.1 = p + v ↔ v + a e.1 = p := by
      constructor
      · intro h'; rw [h', add_comm p v, ← add_assoc, hvv, zero_add]
      · intro h'; rw [← h', add_comm v (a e.1), add_assoc, hvv, add_zero]
    rw [i1, i2]
    tauto
  -- `∑ₚ N p = 2 |M|`
  have hNsum : ∑ p, N p = 2 * M.card := by
    simp only [hN, card_filter]
    rw [Finset.sum_comm]
    have : ∀ e ∈ M, (∑ p : Fin k → ZMod 2, if a e.1 = p ∨ a e.2 = p then 1 else 0) = 2 := by
      intro e he
      have hne : a e.1 ≠ a e.2 := by
        intro h
        apply hv
        rw [← hsum e he, h, add_self_zmod_two]
      rw [← card_filter]
      have : (univ.filter fun p => a e.1 = p ∨ a e.2 = p) = {a e.1, a e.2} := by
        ext p; simp [eq_comm]
      rw [this, card_pair hne]
    rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_comm]
  rw [← hNsum]
  refine sum_le_sum fun p _ => le_min (hNle p) ?_
  rw [← hNeq p]
  exact hNle (p + v)

/-! ### Linear two-query locally decodable codes -/

/-- A **linear two-query locally decodable code in matching form** with parameter `δ`: the code
is given by `m` vectors `a j ∈ 𝔽₂ᵏ` (the codeword of `x` is `(⟨a j, x⟩)_j`), and for every message
index `i` there is a matching `M` on the positions with at least `δ m` pairs, each pair `(u, v)`
satisfying `a u + a v = eᵢ`. -/
def IsLinearTwoQueryLDC {k m : ℕ} (a : Fin m → Fin k → ZMod 2) (δ : ℝ) : Prop :=
  ∀ i : Fin k, ∃ M : Finset (Fin m × Fin m), IsPairMatching M ∧
    (∀ e ∈ M, a e.1 + a e.2 = Pi.single i 1) ∧ δ * m ≤ M.card

private lemma single_ne_zero {k : ℕ} (i : Fin k) : (Pi.single i 1 : Fin k → ZMod 2) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

/-- The sum of the matching sizes is at most half the weighted edge count. -/
theorem IsLinearTwoQueryLDC.mul_le_cubeEdgeWeight {k m : ℕ} {a : Fin m → Fin k → ZMod 2}
    {δ : ℝ} (h : IsLinearTwoQueryLDC a δ) :
    2 * (k * (δ * m)) ≤ (cubeEdgeWeight (fiberCount a) : ℝ) := by
  choose M hM hsum hcard using h
  have hi : ∀ i, 2 * (δ * m) ≤ ((∑ p, min (fiberCount a p)
      (fiberCount a (p + Pi.single i 1)) : ℕ) : ℝ) := by
    intro i
    have := two_mul_card_le_sum_min a (hM i) (single_ne_zero i) (hsum i)
    have h' : (2 * (M i).card : ℝ) ≤ ((∑ p, min (fiberCount a p)
        (fiberCount a (p + Pi.single i 1)) : ℕ) : ℝ) := by exact_mod_cast this
    linarith [hcard i]
  have := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin k))) => hi i
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  unfold cubeEdgeWeight
  push_cast at this ⊢
  linarith

/-- **Linear two-query LDCs need exponential length** (in the matching form, a bound of the type
of Goldreich–Karloff–Schulman–Trevisan). If `m ≥ 1` vectors `a j ∈ 𝔽₂ᵏ` admit, for every
`i < k`, a matching of at least `δ m` pairs `(u, v)` with `a u + a v = eᵢ`, then
`m ≥ 4 ^ (δ k)`. -/
theorem IsLinearTwoQueryLDC.four_rpow_le {k m : ℕ} {a : Fin m → Fin k → ZMod 2} {δ : ℝ}
    (h : IsLinearTwoQueryLDC a δ) (hm : 0 < m) : (4 : ℝ) ^ (δ * k) ≤ m := by
  have h1 := h.mul_le_cubeEdgeWeight
  have h2 := cubeEdgeWeight_mul_log_two_le (fiberCount a)
  rw [sum_fiberCount] at h2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hl2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have h3 : (m : ℝ) * (2 * δ * k * log 2) ≤ m * log m := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hl2]
  have h4 : 2 * δ * k * log 2 ≤ log m := le_of_mul_le_mul_left h3 hmR
  rw [rpow_def_of_pos (by norm_num), ← exp_log hmR]
  apply exp_le_exp.mpr
  have : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  rw [this]
  linarith

/-- The same bound with base `2`: `m ≥ 2 ^ (2 δ k)`. -/
theorem IsLinearTwoQueryLDC.two_rpow_le {k m : ℕ} {a : Fin m → Fin k → ZMod 2} {δ : ℝ}
    (h : IsLinearTwoQueryLDC a δ) (hm : 0 < m) : (2 : ℝ) ^ (2 * δ * k) ≤ m := by
  have := h.four_rpow_le hm
  rwa [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← rpow_mul (by norm_num), ← mul_assoc] at this

end Applied.Coding
