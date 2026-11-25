import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Optimal selling to a single buyer: a posted price is optimal (finite support)

A seller faces one buyer whose value lies in a finite set `s : Finset ℝ` of non-negative
reals; the value `v ∈ s` has weight (probability) `w v ≥ 0`. A direct mechanism is a pair of
an allocation rule `x : ℝ → ℝ` (probability of sale) and a payment rule `p : ℝ → ℝ`.

* `tail s w r = ∑ v ∈ s with r ≤ v, w v`: the probability that the value is at least `r`
  (this is `1 - F(r⁻)` for the cdf `F`).
* `revenue s w p = ∑ v ∈ s, w v * p v`: expected revenue.
* `IsFeasible s x p`: on the support, `0 ≤ x ≤ 1`, the buyer's utility `v * x v - p v` is
  non-negative (individual rationality), and reporting the true value is at least as good as
  reporting any other value of the support (incentive compatibility).
* `postedX r`, `postedP r`: the posted-price mechanism "sell at price `r` iff `r ≤ v`".
* `revenue_le_posted_price`: the revenue of any feasible mechanism is at most
  `r * tail s w r` for some `r` in the support.
* `exists_optimal_posted_price`: some posted price `r` in the support is feasible and earns at
  least as much as every feasible mechanism.

The weights are not required to sum to one (the statements are homogeneous in `w`). Only the
finite-support case is treated; no integrals are involved.
-/

open Finset

namespace Applied.Economics.MonopolyPricing

/-- Total weight of the values that are at least `r`: the probability of a sale at posted
price `r`. -/
noncomputable def tail (s : Finset ℝ) (w : ℝ → ℝ) (r : ℝ) : ℝ := ∑ v ∈ s with r ≤ v, w v

/-- Expected revenue of the payment rule `p`. -/
def revenue (s : Finset ℝ) (w p : ℝ → ℝ) : ℝ := ∑ v ∈ s, w v * p v

/-- A feasible direct mechanism on the support `s`: sale probabilities in `[0, 1]`,
individual rationality and incentive compatibility. -/
structure IsFeasible (s : Finset ℝ) (x p : ℝ → ℝ) : Prop where
  nonneg : ∀ v ∈ s, 0 ≤ x v
  le_one : ∀ v ∈ s, x v ≤ 1
  rational : ∀ v ∈ s, 0 ≤ v * x v - p v
  truthful : ∀ v ∈ s, ∀ b ∈ s, v * x b - p b ≤ v * x v - p v

/-- Allocation rule of the posted price `r`: sell iff the value is at least `r`. -/
noncomputable def postedX (r : ℝ) (v : ℝ) : ℝ := if r ≤ v then 1 else 0

/-- Payment rule of the posted price `r`: pay `r` iff the value is at least `r`. -/
noncomputable def postedP (r : ℝ) (v : ℝ) : ℝ := if r ≤ v then r else 0

/-- The tail weight `tail s w r` is non-negative when all weights are. -/
lemma tail_nonneg {s : Finset ℝ} {w : ℝ → ℝ} (hw : ∀ v ∈ s, 0 ≤ w v) (r : ℝ) :
    0 ≤ tail s w r :=
  Finset.sum_nonneg fun v hv => hw v (Finset.mem_filter.mp hv).1

/-- The revenue of a posted price `r` is `r` times the probability of a sale. -/
theorem revenue_posted (s : Finset ℝ) (w : ℝ → ℝ) (r : ℝ) :
    revenue s w (postedP r) = r * tail s w r := by
  simp only [revenue, tail, postedP, mul_ite, mul_zero, Finset.mul_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun v _ => by split_ifs <;> ring

/-- A posted price is truthful for every real value and report. -/
theorem posted_truthful (r v b : ℝ) :
    v * postedX r b - postedP r b ≤ v * postedX r v - postedP r v := by
  simp only [postedX, postedP]
  split_ifs with h1 h2 h2 <;> linarith

/-- A posted price is individually rational for every real value. -/
theorem posted_rational (r v : ℝ) : 0 ≤ v * postedX r v - postedP r v := by
  simp only [postedX, postedP]
  split_ifs with h <;> linarith

/-- Posted prices are feasible mechanisms. -/
theorem posted_isFeasible (s : Finset ℝ) (r : ℝ) : IsFeasible s (postedX r) (postedP r) where
  nonneg v _ := by simp only [postedX]; split_ifs <;> norm_num
  le_one v _ := by simp only [postedX]; split_ifs <;> norm_num
  rational v _ := posted_rational r v
  truthful v _ b _ := posted_truthful r v b

/-- Induction behind the revenue bound, adding support points from the largest down. -/
private lemma revenue_le_aux (w : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R) (s : Finset ℝ) :
    (∀ v ∈ s, 0 ≤ w v) → (∀ u ∈ s, u * tail s w u ≤ R) → ∀ (x p : ℝ → ℝ) (c : ℝ), 0 ≤ c →
      (∀ v ∈ s, 0 ≤ x v) → (∀ v ∈ s, x v ≤ c) →
      (∀ b ∈ s, ∀ v ∈ s, b ≤ v → x b ≤ x v) →
      (∀ v ∈ s, p v ≤ v * x v) →
      (∀ v ∈ s, ∀ b ∈ s, v * x b - p b ≤ v * x v - p v) →
      ∑ v ∈ s, w v * p v ≤ R * c := by
  induction s using Finset.induction_on_min with
  | empty =>
    intro _ _ x p c hc _ _ _ _ _
    simpa using mul_nonneg hR hc
  | insert a s ha ih =>
    intro hw htail x p c hc hx0 hxc hmono hIR hIC
    have has : a ∉ s := fun h => lt_irrefl _ (ha a h)
    have hmem : ∀ v ∈ s, v ∈ insert a s := fun v hv => Finset.mem_insert_of_mem hv
    have hamem : a ∈ insert a s := Finset.mem_insert_self a s
    have htail' : ∀ u ∈ s, tail (insert a s) w u = tail s w u := by
      intro u hu
      simp [tail, Finset.filter_insert, not_le.mpr (ha u hu)]
    have htaila : tail (insert a s) w a = w a + ∑ v ∈ s, w v := by
      have hfil : (insert a s).filter (fun v => a ≤ v) = insert a s := by
        refine Finset.filter_true_of_mem fun v hv => ?_
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact le_rfl
        · exact (ha v hv).le
      simp only [tail, hfil, Finset.sum_insert has]
    have hIH := ih (fun v hv => hw v (hmem v hv))
      (fun u hu => by rw [← htail' u hu]; exact htail u (hmem u hu))
      (fun v => x v - x a) (fun v => p v - a * x a) (c - x a)
      (by linarith [hxc a hamem])
      (fun v hv => by
        have := hmono a hamem v (hmem v hv) (ha v hv).le
        linarith)
      (fun v hv => by linarith [hxc v (hmem v hv)])
      (fun b hb v hv hbv => by
        have := hmono b (hmem b hb) v (hmem v hv) hbv
        linarith)
      (fun v hv => by
        have h1 := hIC v (hmem v hv) a hamem
        have h2 := hIR a hamem
        nlinarith)
      (fun v hv b hb => by
        have := hIC v (hmem v hv) b (hmem b hb)
        nlinarith)
    have hsplit : ∑ v ∈ s, w v * (p v - a * x a) =
        ∑ v ∈ s, w v * p v - a * x a * ∑ v ∈ s, w v := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsplit] at hIH
    rw [Finset.sum_insert has]
    have h1 : w a * p a ≤ w a * (a * x a) :=
      mul_le_mul_of_nonneg_left (hIR a hamem) (hw a hamem)
    have h2 := htail a hamem
    rw [htaila] at h2
    have h3 : x a * (a * (w a + ∑ v ∈ s, w v)) ≤ x a * R :=
      mul_le_mul_of_nonneg_left h2 (hx0 a hamem)
    nlinarith

/-- Incentive compatibility on the support forces the allocation rule to be monotone there. -/
lemma IsFeasible.monotoneOn {s : Finset ℝ} {x p : ℝ → ℝ} (h : IsFeasible s x p) :
    ∀ b ∈ s, ∀ v ∈ s, b ≤ v → x b ≤ x v := by
  intro b hb v hv hbv
  rcases hbv.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have h1 := h.truthful v hv b hb
    have h2 := h.truthful b hb v hv
    by_contra hcon
    rw [not_le] at hcon
    nlinarith

/-- Revenue bound in terms of any bound `R` on posted-price revenues: if `u * P(value ≥ u) ≤ R`
for every `u` in the support, then every feasible mechanism earns at most `R`. -/
theorem revenue_le_of_tail_le {s : Finset ℝ} {w : ℝ → ℝ} (hw : ∀ v ∈ s, 0 ≤ w v) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ u ∈ s, u * tail s w u ≤ R) {x p : ℝ → ℝ} (h : IsFeasible s x p) :
    revenue s w p ≤ R := by
  have := revenue_le_aux w R hR0 s hw hR x p 1 zero_le_one h.nonneg h.le_one
    h.monotoneOn (fun v hv => by linarith [h.rational v hv]) h.truthful
  simpa [revenue] using this

/-- **Posted prices are optimal, revenue bound.** For a buyer with finitely many possible
non-negative values, every feasible mechanism earns at most `r * P(value ≥ r)` for some `r` in
the support. -/
theorem revenue_le_posted_price {s : Finset ℝ} (hs : s.Nonempty) {w : ℝ → ℝ}
    (hw : ∀ v ∈ s, 0 ≤ w v) (hs0 : ∀ v ∈ s, 0 ≤ v) :
    ∃ r ∈ s, ∀ x p : ℝ → ℝ, IsFeasible s x p → revenue s w p ≤ r * tail s w r := by
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image s (fun u => u * tail s w u) hs
  refine ⟨r, hr, fun x p h => ?_⟩
  have hR : 0 ≤ r * tail s w r := mul_nonneg (hs0 r hr) (tail_nonneg hw r)
  have := revenue_le_aux w (r * tail s w r) hR s hw hmax x p 1 zero_le_one h.nonneg h.le_one
    h.monotoneOn (fun v hv => by linarith [h.rational v hv]) h.truthful
  simpa [revenue] using this

/-- **A posted price is an optimal mechanism** (single buyer, finite support): there is a
price `r` in the support whose posted-price mechanism is feasible and earns at least as much
as every feasible mechanism. -/
theorem exists_optimal_posted_price {s : Finset ℝ} (hs : s.Nonempty) {w : ℝ → ℝ}
    (hw : ∀ v ∈ s, 0 ≤ w v) (hs0 : ∀ v ∈ s, 0 ≤ v) :
    ∃ r ∈ s, IsFeasible s (postedX r) (postedP r) ∧
      ∀ x p : ℝ → ℝ, IsFeasible s x p → revenue s w p ≤ revenue s w (postedP r) := by
  obtain ⟨r, hr, h⟩ := revenue_le_posted_price hs hw hs0
  exact ⟨r, hr, posted_isFeasible s r, fun x p hxp => by
    rw [revenue_posted]; exact h x p hxp⟩

end Applied.Economics.MonopolyPricing
