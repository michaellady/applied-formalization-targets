import Applied.Economics.MatroidSecretary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The classical secretary problem: exact success probability and the `1/e` bound

This file continues `Applied/Economics/MatroidSecretary.lean` and uses its model: arrival
orders `σ : Fin n ≃ E` (`n = Fintype.card E`, times `0, …, n - 1`), online algorithms, and the
threshold rule `thresholdRule r κ` ("skip the first `r` arrivals, then accept the first arrival
whose key is strictly larger than the keys of all earlier arrivals").

## Results

Throughout, the keys `κ (e, w e)` are pairwise distinct and `b` is the element of largest key.
`S r` denotes the set of arrival orders in which `thresholdRule r κ` accepts `b`.

* `card_thresholdRule_success_mul` (exact count, `r ≥ 1`):
  `#S r * n = n! * r * ∑_{t = r}^{n - 1} 1/t` (in `ℝ`). For `r ≥ n` both sides are `0`.
* `card_thresholdRule_success_zero` (`r = 0`): `#S 0 * n = n!`.
* `thresholdRule_success_prob` / `thresholdRule_success_prob'`: the same as a probability,
  `#S r / n! = (r / n) * ∑_{t = r}^{n - 1} 1/t = (r / n) * ∑_{i = r + 1}^{n} 1/(i - 1)`.
* `thresholdRule_success_one_div_e`: with `r = ⌊n / e⌋`, `n! ≤ e * #S r`, i.e. the rule accepts
  the best element with probability at least `1/e`, for every `n ≥ 1` (no error term).
* `secretary_rule_one_div_e`: the same for distinct real weights (`secretaryRule E`);
  `secretary_threshold_prob`: the exact probability for distinct real weights.
* `secretaryRuleLex_isCompetitive`, `exists_isCompetitive_rankOne_inv_exp`: for the rank-one
  uniform matroid, the `⌊n/e⌋` rule with ties broken by a fixed order of `E` is feasible and
  `1/e`-competitive for arbitrary non-negative weights.

Auxiliary analytic facts: `log_div_le_trapezoid` (`log (1 + 1/t) ≤ (1/t + 1/(t+1))/2`),
`log_add_le_sum_inv` (`log (m/r) + (1/r - 1/m)/2 ≤ ∑_{t=r}^{m-1} 1/t`).

Not proved: optimality of the threshold rule among all online stopping rules.
-/

open Finset Function

open scoped Nat

open Classical

noncomputable section

namespace Applied.Economics.MatroidSecretary

variable {E : Type*} [Fintype E]

section Exact

variable {α : Type*} [LinearOrder α]

/-- The arrival orders in which `b` arrives at time `t` and, among the first `t` arrivals,
the one at time `j` has the strictly largest key. -/
def prefMax (f : E → α) (b : E) (t : ℕ) (j : Fin (Fintype.card E)) :
    Finset (ArrivalOrder E) :=
  univ.filter fun σ => (σ.symm b : ℕ) = t ∧
    ∀ i : Fin (Fintype.card E), (i : ℕ) < t → i ≠ j → f (σ i) < f (σ j)

lemma swap_val_lt {n t : ℕ} {j j' i : Fin n} (hj : (j : ℕ) < t) (hj' : (j' : ℕ) < t)
    (hi : (i : ℕ) < t) : ((Equiv.swap j j' i : Fin n) : ℕ) < t := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

lemma swap_eq_self_of_val {n t : ℕ} {j j' p : Fin n} (hj : (j : ℕ) < t) (hj' : (j' : ℕ) < t)
    (hp : (p : ℕ) = t) : Equiv.swap j j' p = p := by
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> intro h <;> subst h <;> omega

/-- Under a uniformly random arrival order, the time of the maximum of the first `t` arrivals
is uniform over `{0, …, t - 1}`, also conditionally on the arrival time `t` of `b`. -/
lemma card_prefMax_eq (f : E → α) (b : E) (t : ℕ) {j j' : Fin (Fintype.card E)}
    (hj : (j : ℕ) < t) (hj' : (j' : ℕ) < t) : #(prefMax f b t j) = #(prefMax f b t j') := by
  refine Finset.card_equiv ((Equiv.swap j j').equivCongr (Equiv.refl E)) fun σ => ?_
  have e1 : ∀ x : E, ((Equiv.swap j j').equivCongr (Equiv.refl E) σ).symm x =
      Equiv.swap j j' (σ.symm x) := by
    intro x
    rw [Equiv.symm_apply_eq]
    simp [Equiv.equivCongr_apply_apply]
  have e2 : ∀ i, ((Equiv.swap j j').equivCongr (Equiv.refl E) σ) i = σ (Equiv.swap j j' i) := by
    intro i
    simp [Equiv.equivCongr_apply_apply]
  simp only [prefMax, mem_filter, mem_univ, true_and, e1, e2, Equiv.swap_apply_right]
  constructor
  · rintro ⟨hb, h⟩
    refine ⟨by rw [swap_eq_self_of_val hj hj' hb]; exact hb, fun i hi hij => ?_⟩
    refine h _ (swap_val_lt hj hj' hi) ?_
    intro hc
    apply hij
    rw [← Equiv.swap_apply_self j j' i, hc, Equiv.swap_apply_left]
  · rintro ⟨hb, h⟩
    have hp : Equiv.swap j j' (σ.symm b) = σ.symm b := by
      have h2 := swap_eq_self_of_val hj hj' hb
      rw [Equiv.swap_apply_self] at h2
      exact h2.symm
    refine ⟨by rw [← hp]; exact hb, fun i hi hij => ?_⟩
    have := h (Equiv.swap j j' i) (swap_val_lt hj hj' hi) (by
      intro hc
      apply hij
      rw [← Equiv.swap_apply_self j j' i, hc, Equiv.swap_apply_right])
    rwa [Equiv.swap_apply_self] at this

/-- The sets `prefMax f b t j` for different `j` are disjoint. -/
lemma disjoint_prefMax (f : E → α) (b : E) (t : ℕ) {j j' : Fin (Fintype.card E)}
    (hj : (j : ℕ) < t) (hj' : (j' : ℕ) < t) (hne : j ≠ j') :
    Disjoint (prefMax f b t j) (prefMax f b t j') := by
  rw [Finset.disjoint_left]
  intro σ h1 h2
  simp only [prefMax, mem_filter, mem_univ, true_and] at h1 h2
  exact lt_asymm (h1.2 j' hj' hne.symm) (h2.2 j hj hne)

/-- A union of the sets `prefMax f b t j` over times `j < t` has `#s` times the size of one
of them. -/
lemma card_biUnion_prefMax (f : E → α) (b : E) (t : ℕ) (s : Finset (Fin (Fintype.card E)))
    (hs : ∀ j ∈ s, (j : ℕ) < t) {j₀ : Fin (Fintype.card E)} (hj₀ : (j₀ : ℕ) < t) :
    #(s.biUnion (prefMax f b t)) = #s * #(prefMax f b t j₀) := by
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun j hj => card_prefMax_eq f b t (hs j hj) hj₀, Finset.sum_const,
      smul_eq_mul]
  · intro j hj j' hj' hne
    exact disjoint_prefMax f b t (hs j hj) (hs j' hj') hne

/-- If `b` arrives at time `t ≥ 1`, some time `j < t` carries the strict maximum of the keys
of the first `t` arrivals. -/
lemma exists_prefMax {f : E → α} (hf : Injective f) {b : E} {t : ℕ} (ht : 0 < t)
    (σ : ArrivalOrder E) (hσ : (σ.symm b : ℕ) = t) :
    ∃ j : Fin (Fintype.card E), (j : ℕ) < t ∧ σ ∈ prefMax f b t j := by
  have htn : t < Fintype.card E := hσ ▸ (σ.symm b).isLt
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image
    (univ.filter fun j : Fin (Fintype.card E) => (j : ℕ) < t) (fun j => f (σ j))
    ⟨⟨0, by omega⟩, by simp [ht]⟩
  rw [mem_filter] at hj
  refine ⟨j, hj.2, ?_⟩
  simp only [prefMax, mem_filter, mem_univ, true_and]
  refine ⟨hσ, fun i hi hij => lt_of_le_of_ne (hmax i (by simp [hi])) fun h => hij ?_⟩
  exact σ.injective (hf h)

/-- `n * #{σ | b arrives at time t} = n!`. -/
lemma card_mul_card_arrive (b : E) {t : ℕ} (ht : t < Fintype.card E) :
    (Fintype.card E : ℝ) * #{σ : ArrivalOrder E | (σ.symm b : ℕ) = t} = (Fintype.card E)! := by
  have h := card_mul_sum_orders_apply (fun e => if e = b then (1 : ℝ) else 0) ⟨t, ht⟩
  have h1 : #{x : E | x = b} = 1 := Finset.card_eq_one.2 ⟨b, by ext; simp⟩
  simp only [Finset.sum_boole] at h
  rw [h1, Nat.cast_one, mul_one] at h
  convert h using 4
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    rw [show (⟨t, ht⟩ : Fin _) = σ.symm b from Fin.ext h.symm]
    simp
  · intro h
    rw [← h]
    simp

/-- `#{σ | b arrives at time t} = t * #(prefMax f b t j₀)` for `1 ≤ t`, `j₀ < t`. -/
lemma card_arrive_eq {f : E → α} (hf : Injective f) (b : E) {t : ℕ} (ht : 0 < t)
    {j₀ : Fin (Fintype.card E)} (hj₀ : (j₀ : ℕ) < t) (htn : t < Fintype.card E) :
    #{σ : ArrivalOrder E | (σ.symm b : ℕ) = t} = t * #(prefMax f b t j₀) := by
  have hset : (univ.filter fun σ : ArrivalOrder E => (σ.symm b : ℕ) = t) =
      (univ.filter fun j : Fin (Fintype.card E) => (j : ℕ) < t).biUnion (prefMax f b t) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · intro hσ
      obtain ⟨j, hj, hmem⟩ := exists_prefMax hf ht σ hσ
      exact ⟨j, hj, hmem⟩
    · rintro ⟨j, -, hmem⟩
      simp only [prefMax, mem_filter, mem_univ, true_and] at hmem
      exact hmem.1
  rw [hset, card_biUnion_prefMax f b t _ (fun j hj => (mem_filter.1 hj).2) hj₀,
    Fin.card_filter_val_lt]
  congr 1
  omega

variable (κ : E × ℝ → α) (w : E → ℝ)

/-- For `r ≥ 1` and `r ≤ t`: the orders in which `b` arrives at time `t` and is accepted by
`thresholdRule r κ` are those in which the maximum of the first `t` keys arrives before `r`. -/
lemma success_at_eq (hinj : Injective fun e => κ (e, w e)) (b : E)
    (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) {r t : ℕ} (hr : 0 < r) (hrt : r ≤ t) :
    (univ.filter fun σ : ArrivalOrder E =>
        b ∈ selected (thresholdRule r κ) σ w ∧ (σ.symm b : ℕ) = t) =
      (univ.filter fun j : Fin (Fintype.card E) => (j : ℕ) < r).biUnion
        (prefMax (fun e => κ (e, w e)) b t) := by
  have hblt : ∀ e, e ≠ b → κ (e, w e) < κ (b, w b) := fun e he =>
    lt_of_le_of_ne (hb e) fun h => he (hinj h)
  ext σ
  simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_selected, accepts_thresholdRule]
  constructor
  · rintro ⟨⟨-, -, h3⟩, hσ⟩
    obtain ⟨j, hj, hmem⟩ := exists_prefMax hinj (by omega) σ hσ
    refine ⟨j, ?_, hmem⟩
    by_contra hjr
    push Not at hjr
    simp only [prefMax, mem_filter, mem_univ, true_and] at hmem
    obtain ⟨j', hj', hle⟩ := h3 j hjr (by rw [Fin.lt_def, hσ]; exact hj)
    have hne : j' ≠ j := by intro h; subst h; omega
    have := hmem.2 j' (by omega) hne
    exact absurd this (not_lt.2 hle)
  · rintro ⟨j, hj, hmem⟩
    simp only [prefMax, mem_filter, mem_univ, true_and] at hmem
    obtain ⟨hσ, hmax⟩ := hmem
    refine ⟨⟨by omega, fun i hi => hblt _ fun h => ?_, fun i hri hi => ⟨j, hj, ?_⟩⟩, hσ⟩
    · rw [← h, Equiv.symm_apply_apply] at hi
      exact lt_irrefl _ hi
    · have hi' : (i : ℕ) < t := by rw [← hσ]; exact hi
      exact (hmax i hi' fun h => by subst h; omega).le

/-- **Exact success probability of the threshold rule (counting form).** Let `n = |E|`, let
the keys `κ (e, w e)` be pairwise distinct and let `b` have the largest key. For `r ≥ 1`, the
number of arrival orders in which `thresholdRule r κ` accepts `b` satisfies
`#S * n = n! * r * ∑_{t=r}^{n-1} 1/t`. -/
theorem card_thresholdRule_success_mul (hinj : Injective fun e => κ (e, w e)) (b : E)
    (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) {r : ℕ} (hr : 0 < r) :
    (#{σ : ArrivalOrder E | b ∈ selected (thresholdRule r κ) σ w} : ℝ) * Fintype.card E =
      (Fintype.card E)! * r * ∑ t ∈ Ico r (Fintype.card E), (1 : ℝ) / t := by
  set n := Fintype.card E with hn
  have hmaps : ((univ.filter fun σ : ArrivalOrder E => b ∈ selected (thresholdRule r κ) σ w :
      Finset _) : Set (ArrivalOrder E)).MapsTo (fun σ => (σ.symm b : ℕ)) (Ico r n) := by
    intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_selected,
      accepts_thresholdRule] at hσ
    simp only [coe_Ico, Set.mem_Ico]
    exact ⟨hσ.1, (σ.symm b).isLt⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [mem_Ico] at ht
  have ht0 : 0 < t := by omega
  set j₀ : Fin n := ⟨0, by omega⟩
  have hj₀ : (j₀ : ℕ) < t := ht0
  have hj₀r : (j₀ : ℕ) < r := hr
  have hS : #{σ ∈ (univ.filter fun σ : ArrivalOrder E => b ∈ selected (thresholdRule r κ) σ w) |
      (σ.symm b : ℕ) = t} = r * #(prefMax (fun e => κ (e, w e)) b t j₀) := by
    rw [Finset.filter_filter, success_at_eq κ w hinj b hb hr ht.1,
      card_biUnion_prefMax _ b t _ (fun j hj => by have := (mem_filter.1 hj).2; omega) hj₀,
      Fin.card_filter_val_lt]
    congr 1
    omega
  have hB := card_arrive_eq hinj b ht0 hj₀ ht.2
  have hC := card_mul_card_arrive b ht.2
  rw [hB] at hC
  rw [hS]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  push_cast at hC ⊢
  rw [mul_one_div, eq_div_iff htR.ne']
  linear_combination (r : ℝ) * hC

/-- **The case `r = 0`** (accept the first arrival): `#S * n = n!`, probability `1/n`. -/
theorem card_thresholdRule_success_zero (b : E) :
    (#{σ : ArrivalOrder E | b ∈ selected (thresholdRule 0 κ) σ w} : ℝ) * Fintype.card E =
      (Fintype.card E)! := by
  have hpos : 0 < Fintype.card E := Fintype.card_pos_iff.2 ⟨b⟩
  have hset : (univ.filter fun σ : ArrivalOrder E => b ∈ selected (thresholdRule 0 κ) σ w) =
      univ.filter fun σ : ArrivalOrder E => (σ.symm b : ℕ) = 0 := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_selected, accepts_thresholdRule]
    constructor
    · rintro ⟨-, -, h3⟩
      by_contra h
      obtain ⟨j, hj, -⟩ := h3 ⟨0, hpos⟩ (Nat.zero_le _)
        (by rw [Fin.lt_def]; simp only; omega)
      omega
    · intro h
      refine ⟨Nat.zero_le _, fun i hi => ?_, fun i _ hi => ?_⟩ <;>
        · rw [Fin.lt_def, h] at hi; omega
  rw [hset, mul_comm]
  exact card_mul_card_arrive b hpos

/-- **Exact success probability of the threshold rule.** Under a uniformly random arrival
order, for `r ≥ 1` the probability that `thresholdRule r κ` accepts the element `b` of largest
key is `(r / n) * ∑_{t=r}^{n-1} 1/t`. -/
theorem thresholdRule_success_prob (hinj : Injective fun e => κ (e, w e)) (b : E)
    (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) {r : ℕ} (hr : 0 < r) :
    (#{σ : ArrivalOrder E | b ∈ selected (thresholdRule r κ) σ w} : ℝ) / (Fintype.card E)! =
      r / Fintype.card E * ∑ t ∈ Ico r (Fintype.card E), (1 : ℝ) / t := by
  have hpos : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos_iff.2 ⟨b⟩
  have hfac : (0 : ℝ) < (Fintype.card E)! := by exact_mod_cast Nat.factorial_pos _
  have h := card_thresholdRule_success_mul κ w hinj b hb hr
  rw [div_eq_iff hfac.ne']
  field_simp
  linarith

/-- The textbook indexing of the sum: `∑_{t=r}^{n-1} 1/t = ∑_{i=r+1}^{n} 1/(i-1)`. -/
lemma sum_Ico_inv_eq (r n : ℕ) :
    ∑ t ∈ Ico r n, (1 : ℝ) / t = ∑ i ∈ Icc (r + 1) n, (1 : ℝ) / ((i : ℝ) - 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_Ico_add' (fun i : ℕ => (1 : ℝ) / ((i : ℝ) - 1)) r n 1]
  refine Finset.sum_congr rfl fun t _ => ?_
  push_cast
  ring_nf

/-- The exact success probability in the textbook indexing:
`(r / n) * ∑_{i=r+1}^{n} 1/(i-1)` for `r ≥ 1`. -/
theorem thresholdRule_success_prob' (hinj : Injective fun e => κ (e, w e)) (b : E)
    (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) {r : ℕ} (hr : 0 < r) :
    (#{σ : ArrivalOrder E | b ∈ selected (thresholdRule r κ) σ w} : ℝ) / (Fintype.card E)! =
      r / Fintype.card E * ∑ i ∈ Icc (r + 1) (Fintype.card E), (1 : ℝ) / ((i : ℝ) - 1) := by
  rw [thresholdRule_success_prob κ w hinj b hb hr, sum_Ico_inv_eq]

end Exact

section OneOverE

/-- The trapezoid bound for `∫_t^{t+1} dx/x`:
`log ((t + 1) / t) ≤ (1/t + 1/(t + 1)) / 2` for `t > 0`. -/
lemma log_div_le_trapezoid {t : ℝ} (ht : 0 < t) :
    Real.log ((t + 1) / t) ≤ (1 / t + 1 / (t + 1)) / 2 := by
  have ht1 : 0 < t + 1 := by linarith
  have ha : 0 < (t + 1) / t := by positivity
  have h1 : 1 ≤ (t + 1) / t := by rw [le_div_iff₀ ht]; linarith
  have hlog : 0 ≤ Real.log ((t + 1) / t) := Real.log_nonneg h1
  have h := Real.self_le_sinh_iff.2 hlog
  rw [Real.sinh_log ha] at h
  calc _ ≤ _ := h
    _ = _ := by field_simp; ring

/-- `log (m / r) + (1/r - 1/m) / 2 ≤ ∑_{t=r}^{m-1} 1/t` for `1 ≤ r ≤ m`. -/
lemma log_add_le_sum_inv {r : ℕ} (hr : 0 < r) {m : ℕ} (hm : r ≤ m) :
    Real.log (m / r) + (1 / r - 1 / m) / 2 ≤ ∑ t ∈ Ico r m, (1 : ℝ) / t := by
  induction m, hm using Nat.le_induction with
  | base =>
    have : (r : ℝ) ≠ 0 := by positivity
    simp [this]
  | succ m hrm ih =>
    rw [Finset.sum_Ico_succ_top hrm]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le hr hrm
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hsplit : Real.log (((m + 1 : ℕ) : ℝ) / r) =
        Real.log (m / r) + Real.log ((m + 1) / m) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
    have := log_div_le_trapezoid hm0
    rw [hsplit]
    push_cast
    linarith

/-- The analytic core of the `1/e` bound: with `r = ⌊n/e⌋` and `n ≥ 3`,
`n ≤ e * r * ∑_{t=r}^{n-1} 1/t`. -/
lemma le_exp_mul_floor_mul_sum (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) ≤ Real.exp 1 * ⌊(n : ℝ) / Real.exp 1⌋₊ *
      ∑ t ∈ Ico ⌊(n : ℝ) / Real.exp 1⌋₊ n, (1 : ℝ) / t := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  by_cases hn9 : 9 ≤ n
  · set e := Real.exp 1 with he
    set r := ⌊(n : ℝ) / e⌋₊ with hrdef
    have hnR : (9 : ℝ) ≤ n := by exact_mod_cast hn9
    have hn0 : (0 : ℝ) < n := by linarith
    have hr1 : (r : ℝ) ≤ n / e := Nat.floor_le (by positivity)
    have hr2 : (n : ℝ) / e < r + 1 := Nat.lt_floor_add_one _
    have hrpos : 0 < r := by
      rw [hrdef, Nat.floor_pos, le_div_iff₀ he0]
      linarith
    have hrn : r ≤ n := by
      have : (r : ℝ) ≤ n := hr1.trans (div_le_self hn0.le (by linarith))
      exact_mod_cast this
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hrpos
    have hH := log_add_le_sum_inv hrpos hrn
    set H := ∑ t ∈ Ico r n, (1 : ℝ) / t with hHdef
    set y := e * r / n with hydef
    have hy0 : 0 < y := by positivity
    have hy1 : y ≤ 1 := by
      rw [hydef, div_le_one hn0]
      rw [le_div_iff₀ he0] at hr1
      linarith
    have hy2 : 1 - e / n ≤ y := by
      rw [div_lt_iff₀ he0] at hr2
      rw [hydef, sub_le_iff_le_add, ← add_div, le_div_iff₀ hn0]
      linarith
    have hlogy : Real.log y = 1 + Real.log r - Real.log n := by
      rw [hydef, Real.log_div (by positivity) hn0.ne', Real.log_mul he0.ne' hr0.ne', he,
        Real.log_exp]
    have hlognr : Real.log (n / r) = Real.log n - Real.log r :=
      Real.log_div hn0.ne' hr0.ne'
    have hly : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
    have h1 : y * (Real.log (n / r) + (1 / r - 1 / n) / 2) ≤ y * H :=
      mul_le_mul_of_nonneg_left hH hy0.le
    have h2 : y * ((1 / r - 1 / n) / 2) = (e - y) / (2 * n) := by
      rw [hydef]
      field_simp
    have h3 : (1 - y) ^ 2 ≤ (e - y) / (2 * n) := by
      have ha : (1 - y) ^ 2 ≤ (e / n) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hb : (e / n) ^ 2 ≤ (e - y) / (2 * n) := by
        rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        have hq1 : 2 * e ^ 2 ≤ 9 * (e - 1) := by nlinarith
        have hq2 : 9 * (e - 1) ≤ (e - y) * n := by nlinarith
        nlinarith
      linarith
    have h4 : 1 ≤ y * H := by
      have : y * (Real.log (n / r) + (1 / r - 1 / n) / 2) =
          y * (1 - Real.log y) + y * ((1 / r - 1 / n) / 2) := by
        rw [hlognr, hlogy]; ring
      nlinarith
    have h5 : e * r * H = n * (y * H) := by
      rw [hydef]
      field_simp
    rw [h5]
    nlinarith
  · have key : ∀ k : ℕ, ⌊(n : ℝ) / Real.exp 1⌋₊ = k →
        (n : ℝ) ≤ 2.7182818283 * k * ∑ t ∈ Ico k n, (1 : ℝ) / t →
        (n : ℝ) ≤ Real.exp 1 * ⌊(n : ℝ) / Real.exp 1⌋₊ *
          ∑ t ∈ Ico ⌊(n : ℝ) / Real.exp 1⌋₊ n, (1 : ℝ) / t := by
      intro k hk h
      rw [hk]
      have : 0 ≤ (k : ℝ) * ∑ t ∈ Ico k n, (1 : ℝ) / t := by positivity
      nlinarith [mul_nonneg (sub_nonneg.2 he1.le) this]
    have hfl : ∀ k : ℕ, (k : ℝ) * Real.exp 1 ≤ n → (n : ℝ) < (k + 1) * Real.exp 1 →
        ⌊(n : ℝ) / Real.exp 1⌋₊ = k := by
      intro k h1 h2
      rw [Nat.floor_eq_iff (by positivity), le_div_iff₀ he0, div_lt_iff₀ he0]
      exact ⟨h1, h2⟩
    push Not at hn9
    interval_cases n
    · refine key 1 (hfl 1 (by norm_num; linarith) (by norm_num; linarith)) ?_
      simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]; norm_num
    · refine key 1 (hfl 1 (by norm_num; linarith) (by norm_num; linarith)) ?_
      simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]; norm_num
    · refine key 1 (hfl 1 (by norm_num; linarith) (by norm_num; linarith)) ?_
      simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]; norm_num
    · refine key 2 (hfl 2 (by norm_num; linarith) (by norm_num; linarith)) ?_
      simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]; norm_num
    · refine key 2 (hfl 2 (by norm_num; linarith) (by norm_num; linarith)) ?_
      simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]; norm_num
    · refine key 2 (hfl 2 (by norm_num; linarith) (by norm_num; linarith)) ?_
      simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]; norm_num

variable {α : Type*} [LinearOrder α]

/-- **The `1/e` bound (key form).** Let `n = |E| ≥ 1`, let the keys `κ (e, w e)` be pairwise
distinct and let `b` have the largest key. The rule "skip the first `⌊n/e⌋` arrivals, then
accept the first arrival whose key exceeds all earlier keys" accepts `b` in at least `n!/e` of
the `n!` arrival orders: `n! ≤ e * #S`. -/
theorem thresholdRule_success_one_div_e (κ : E × ℝ → α) (w : E → ℝ)
    (hinj : Injective fun e => κ (e, w e)) (b : E) (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) :
    ((Fintype.card E)! : ℝ) ≤ Real.exp 1 *
      #{σ : ArrivalOrder E |
        b ∈ selected (thresholdRule ⌊(Fintype.card E : ℝ) / Real.exp 1⌋₊ κ) σ w} := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hpos : 0 < Fintype.card E := Fintype.card_pos_iff.2 ⟨b⟩
  have hnR : (0 : ℝ) < Fintype.card E := by exact_mod_cast hpos
  have hfac : (0 : ℝ) ≤ (Fintype.card E)! := by positivity
  by_cases hn3 : 3 ≤ Fintype.card E
  · have hn3R : (3 : ℝ) ≤ Fintype.card E := by exact_mod_cast hn3
    have hrpos : 0 < ⌊(Fintype.card E : ℝ) / Real.exp 1⌋₊ := by
      rw [Nat.floor_pos, le_div_iff₀ he0]
      linarith
    have h := card_thresholdRule_success_mul κ w hinj b hb hrpos
    have hle := le_exp_mul_floor_mul_sum (Fintype.card E) hn3
    have := mul_le_mul_of_nonneg_left hle hfac
    refine le_of_mul_le_mul_right ?_ hnR
    nlinarith
  · have hr0 : ⌊(Fintype.card E : ℝ) / Real.exp 1⌋₊ = 0 := by
      rw [Nat.floor_eq_zero, div_lt_one he0]
      have : (Fintype.card E : ℝ) ≤ 2 := by exact_mod_cast (by omega : Fintype.card E ≤ 2)
      linarith
    rw [hr0]
    have h := card_thresholdRule_success_zero κ w b
    have : (Fintype.card E : ℝ) ≤ 2 := by exact_mod_cast (by omega : Fintype.card E ≤ 2)
    have hS : (0 : ℝ) ≤ #{σ : ArrivalOrder E | b ∈ selected (thresholdRule 0 κ) σ w} := by
      positivity
    nlinarith

/-- **The `1/e` bound as a probability:** `1/e ≤ #S / n!`. -/
theorem thresholdRule_success_prob_ge (κ : E × ℝ → α) (w : E → ℝ)
    (hinj : Injective fun e => κ (e, w e)) (b : E) (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) :
    1 / Real.exp 1 ≤
      (#{σ : ArrivalOrder E |
        b ∈ selected (thresholdRule ⌊(Fintype.card E : ℝ) / Real.exp 1⌋₊ κ) σ w} : ℝ) /
        (Fintype.card E)! := by
  have hfac : (0 : ℝ) < (Fintype.card E)! := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_div_iff₀ (Real.exp_pos 1) hfac, one_mul, mul_comm]
  exact thresholdRule_success_one_div_e κ w hinj b hb

/-- The classical secretary rule with the optimal-order threshold: skip the first `⌊n/e⌋`
arrivals, then accept the first arrival strictly heavier than all earlier arrivals. -/
def secretaryRule (E : Type*) [Fintype E] : OnlineAlg E :=
  thresholdRule ⌊(Fintype.card E : ℝ) / Real.exp 1⌋₊ Prod.snd

/-- **The classical secretary problem, `1/e` bound.** For pairwise distinct weights, the rule
"skip the first `⌊n/e⌋` arrivals, then accept the first arrival heavier than all earlier ones"
accepts the heaviest element `b` in at least `n!/e` of the `n!` arrival orders, i.e. with
probability at least `1/e` under a uniformly random arrival order, for every `n ≥ 1`. -/
theorem secretary_rule_one_div_e (w : E → ℝ) (hw : Injective w) (b : E)
    (hb : ∀ e, w e ≤ w b) :
    ((Fintype.card E)! : ℝ) ≤ Real.exp 1 * #{σ : ArrivalOrder E | b ∈ selected (secretaryRule E) σ w} :=
  thresholdRule_success_one_div_e Prod.snd w hw b hb

/-- **The classical secretary problem, exact probability.** For pairwise distinct weights and
`r ≥ 1`, the rule "skip the first `r` arrivals, then accept the first arrival heavier than all
earlier ones" accepts the heaviest element with probability `(r/n) * ∑_{i=r+1}^{n} 1/(i-1)`. -/
theorem secretary_threshold_prob (w : E → ℝ) (hw : Injective w) (b : E)
    (hb : ∀ e, w e ≤ w b) {r : ℕ} (hr : 0 < r) :
    (#{σ : ArrivalOrder E | b ∈ selected (thresholdRule r Prod.snd) σ w} : ℝ) /
        (Fintype.card E)! =
      r / Fintype.card E * ∑ i ∈ Icc (r + 1) (Fintype.card E), (1 : ℝ) / ((i : ℝ) - 1) :=
  thresholdRule_success_prob' Prod.snd w hw b hb hr

end OneOverE

/-! ### The rank-one uniform matroid: a `1/e`-competitive algorithm -/

/-- The `⌊n/e⌋` rule with ties broken by a fixed enumeration of `E`: skip the first `⌊n/e⌋`
arrivals, then accept the first arrival that beats all earlier ones in the lexicographic order
on (weight, index of the element). -/
def secretaryRuleLex (E : Type*) [Fintype E] : OnlineAlg E :=
  thresholdRule (α := ℝ ×ₗ Fin (Fintype.card E)) ⌊(Fintype.card E : ℝ) / Real.exp 1⌋₊
    fun p => toLex (p.2, Fintype.equivFin E p.1)

/-- The `⌊n/e⌋` rule accepts at most one element, so it is feasible for the rank-one matroid. -/
theorem secretaryRuleLex_isFeasible : IsFeasible (rankOne E) (secretaryRuleLex E) :=
  fun σ w _ => rankOne_indep_iff.2 (selected_thresholdRule_subsingleton _ _ σ w)

/-- The `⌊n/e⌋` rule (with ties broken by a fixed order) is `1/e`-competitive for the rank-one
uniform matroid: for arbitrary non-negative weights (ties allowed), its expected weight is at
least `1/e` times the largest weight. -/
theorem secretaryRuleLex_isCompetitive :
    IsCompetitive (rankOne E) (secretaryRuleLex E) (1 / Real.exp 1) := by
  intro w hw I hI
  rw [rankOne_indep_iff] at hI
  rcases I.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · simpa using expWeight_nonneg (secretaryRuleLex E) hw
  have hIe : I = {e₀} := Finset.eq_singleton_iff_unique_mem.2 ⟨he₀, fun x hx => hI hx he₀⟩
  set κ : E × ℝ → ℝ ×ₗ Fin (Fintype.card E) := fun p => toLex (p.2, Fintype.equivFin E p.1)
    with hκ
  have hinj : Injective fun e => κ (e, w e) := by
    intro e e' h
    simp only [hκ, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at h
    exact h.2
  obtain ⟨b, -, hbmax⟩ := Finset.exists_max_image (univ : Finset E) (fun e => κ (e, w e))
    ⟨e₀, mem_univ _⟩
  have hb : ∀ e, κ (e, w e) ≤ κ (b, w b) := fun e => hbmax e (mem_univ _)
  have hwb : ∀ e, w e ≤ w b := by
    intro e
    have := hb e
    simp only [hκ, Prod.Lex.toLex_le_toLex] at this
    rcases this with h | h
    · exact h.le
    · exact h.1.le
  have hcount := thresholdRule_success_one_div_e κ w hinj b hb
  set S : Finset (ArrivalOrder E) :=
    univ.filter fun σ : ArrivalOrder E => b ∈ selected (secretaryRuleLex E) σ w with hS
  have hsum : (#S : ℝ) * w b ≤
      ∑ σ : ArrivalOrder E, ∑ e ∈ selected (secretaryRuleLex E) σ w, w e := by
    calc (#S : ℝ) * w b = ∑ σ : ArrivalOrder E, if b ∈ selected (secretaryRuleLex E) σ w then w b
          else 0 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          split_ifs with h
          · exact Finset.single_le_sum (fun e _ => hw e) h
          · exact Finset.sum_nonneg fun e _ => hw e
  have hfac : (0 : ℝ) < (Fintype.card E)! := by exact_mod_cast Nat.factorial_pos _
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hcount' : ((Fintype.card E)! : ℝ) ≤ Real.exp 1 * #S := hcount
  rw [hIe, Finset.sum_singleton, expWeight, le_div_iff₀ hfac]
  have h1 : 1 / Real.exp 1 * w e₀ * (Fintype.card E)! ≤
      1 / Real.exp 1 * w b * (Real.exp 1 * #S) := by
    have := hwb e₀
    have := hw e₀
    have := hw b
    gcongr
  have h2 : 1 / Real.exp 1 * w b * (Real.exp 1 * #S) = #S * w b := by
    field_simp
  linarith

/-- The matroid secretary problem for rank-one uniform matroids (the classical secretary
problem with arbitrary non-negative weights) has a feasible deterministic `1/e`-competitive
online algorithm. -/
theorem exists_isCompetitive_rankOne_inv_exp (E : Type*) [Fintype E] :
    ∃ A : OnlineAlg E, IsFeasible (rankOne E) A ∧ IsCompetitive (rankOne E) A (1 / Real.exp 1) :=
  ⟨secretaryRuleLex E, secretaryRuleLex_isFeasible, secretaryRuleLex_isCompetitive⟩

end Applied.Economics.MatroidSecretary
