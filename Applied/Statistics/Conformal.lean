import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Exchangeability and the conformal prediction coverage guarantee

* `Exchangeable P X`: the joint law of the family `X` is invariant under permutations.
* `Exchangeable.comp`: applying one fixed measurable map to every coordinate preserves
  exchangeability.
* `card_filter_le_card_lt_le`: among `N` real numbers, at most `N - k` have at least `k`
  others strictly below them.
* `Exchangeable.measure_le_card_lt_le`: for exchangeable real random variables, the chance
  that a given one has at least `k` of the others strictly below it is at most `(N - k) / N`.
* `conformal_miscoverage_le`: the split conformal guarantee. With `n` calibration scores and
  one test score, exchangeable, the test score exceeds the `k`-th smallest calibration score
  with probability at most `α` whenever `k ≥ (1 - α)(n + 1)`.

No assumption is made on the distribution of the scores, and ties are allowed.

## Relation to other files and scope

`ConformalExact.lean` adds the matching upper bound on coverage when ties have probability
zero. Not here: the translation of the counting event into an empirical quantile of the
calibration scores, full and cross-conformal prediction, conditional coverage, and coverage
under distribution shift.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.Conformal

variable {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The family `X` is exchangeable under `P`: permuting the indices does not change the joint
law. -/
def Exchangeable (P : Measure Ω) (X : ι → Ω → E) : Prop :=
  ∀ σ : Equiv.Perm ι, P.map (fun ω i => X (σ i) ω) = P.map (fun ω i => X i ω)

/-- Applying the same measurable map to each coordinate preserves exchangeability. This is why
conformal scores computed with a fixed (pre-trained) score function are exchangeable whenever
the data points are. -/
theorem Exchangeable.comp {F : Type*} [MeasurableSpace F] {P : Measure Ω} {X : ι → Ω → E}
    (hX : Exchangeable P X) (hmeas : ∀ i, Measurable (X i)) {s : E → F} (hs : Measurable s) :
    Exchangeable P (fun i ω => s (X i ω)) := by
  intro σ
  have hS : Measurable fun (x : ι → E) (i : ι) => s (x i) :=
    measurable_pi_iff.mpr fun i => hs.comp (measurable_pi_apply i)
  have h1 : (fun ω i => s (X (σ i) ω)) = (fun (x : ι → E) i => s (x i)) ∘ fun ω i => X (σ i) ω :=
    rfl
  have h2 : (fun ω i => s (X i ω)) = (fun (x : ι → E) i => s (x i)) ∘ fun ω i => X i ω := rfl
  rw [h1, h2, ← Measure.map_map hS (measurable_pi_iff.mpr fun i => hmeas (σ i)),
    ← Measure.map_map hS (measurable_pi_iff.mpr hmeas), hX σ]

section Counting

variable [Fintype ι]

/-- Among finitely many real numbers, at most `N - k` of them have at least `k` others
strictly below. -/
theorem card_filter_le_card_lt_le (x : ι → ℝ) (k : ℕ) :
    (univ.filter fun i => k ≤ (univ.filter fun j => x j < x i).card).card + k
      ≤ Fintype.card ι ∨
    (univ.filter fun i => k ≤ (univ.filter fun j => x j < x i).card) = ∅ := by
  classical
  set A := univ.filter fun i => k ≤ (univ.filter fun j => x j < x i).card with hA
  rcases A.eq_empty_or_nonempty with h | hne
  · exact Or.inr h
  · left
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image A x hne
    set B := univ.filter fun j => x j < x i with hB
    have hk : k ≤ B.card := (mem_filter.mp hi).2
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro l hlA hlB
      exact absurd (hmin l hlA) (not_le.mpr (mem_filter.mp hlB).2)
    have : A.card + B.card ≤ Fintype.card ι := by
      rw [← Finset.card_union_of_disjoint hdisj]; exact Finset.card_le_univ _
    omega

/-- Subtraction form of `card_filter_le_card_lt_le`: at most `N - k` of `N` real numbers have at
least `k` others strictly below (natural-number subtraction, so the bound is `0` for `k > N`). -/
theorem card_filter_le_card_lt_le' (x : ι → ℝ) (k : ℕ) :
    (univ.filter fun i => k ≤ (univ.filter fun j => x j < x i).card).card
      ≤ Fintype.card ι - k := by
  rcases card_filter_le_card_lt_le x k with h | h
  · omega
  · rw [h]; simp

end Counting

section Main

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The event "coordinate `i` has at least `k` coordinates strictly below it" is a measurable
subset of `ι → ℝ`. -/
lemma measurableSet_le_card_lt (k : ℕ) (i : ι) :
    MeasurableSet {x : ι → ℝ | k ≤ (univ.filter fun j => x j < x i).card} := by
  classical
  have hcount : Measurable fun x : ι → ℝ => (univ.filter fun j => x j < x i).card := by
    have : (fun x : ι → ℝ => (univ.filter fun j => x j < x i).card)
        = fun x => ∑ j, if x j < x i then 1 else 0 := by
      funext x; rw [Finset.card_filter]
    rw [this]
    exact Finset.measurable_sum _ fun j _ =>
      Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))
        measurable_const measurable_const
  exact measurableSet_le measurable_const hcount

/-- For exchangeable real random variables, every index has the same chance of having at
least `k` of the others strictly below it. -/
theorem Exchangeable.measure_le_card_lt_eq {P : Measure Ω} {X : ι → Ω → ℝ}
    (hX : Exchangeable P X) (hmeas : ∀ i, Measurable (X i)) (k : ℕ) (i i₀ : ι) :
    P {ω | k ≤ (univ.filter fun j => X j ω < X i ω).card}
      = P {ω | k ≤ (univ.filter fun j => X j ω < X i₀ ω).card} := by
  set σ : Equiv.Perm ι := Equiv.swap i i₀ with hσ
  have hXm : Measurable fun ω l => X l ω := measurable_pi_iff.mpr hmeas
  have hXσm : Measurable fun ω l => X (σ l) ω := measurable_pi_iff.mpr fun l => hmeas (σ l)
  have hT := measurableSet_le_card_lt (ι := ι) k i
  have h1 : P {ω | k ≤ (univ.filter fun j => X j ω < X i ω).card}
      = P.map (fun ω l => X l ω) {x : ι → ℝ | k ≤ (univ.filter fun j => x j < x i).card} := by
    rw [Measure.map_apply hXm hT]; rfl
  have h2 : P {ω | k ≤ (univ.filter fun j => X j ω < X i₀ ω).card}
      = P.map (fun ω l => X (σ l) ω)
          {x : ι → ℝ | k ≤ (univ.filter fun j => x j < x i).card} := by
    rw [Measure.map_apply hXσm hT]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    have hσi : σ i = i₀ := Equiv.swap_apply_left i i₀
    have hcard : (univ.filter fun j => X (σ j) ω < X (σ i) ω).card
        = (univ.filter fun j => X j ω < X i₀ ω).card := by
      rw [hσi]
      refine Finset.card_bij (fun j _ => σ j) (fun j hj => ?_) (fun a _ b _ h => σ.injective h)
        (fun b hb => ⟨σ.symm b, ?_, by simp⟩)
      · simpa using hj
      · simpa using hb
    rw [hcard]
  rw [h1, h2, hX σ]

/-- **Rank lemma for exchangeable variables.** The chance that a given one of `N` exchangeable
real random variables has at least `k` of the others strictly below it is at most
`(N - k) / N`. -/
theorem Exchangeable.measure_le_card_lt_le {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} (hX : Exchangeable P X) (hmeas : ∀ i, Measurable (X i)) (k : ℕ) (i₀ : ι) :
    P {ω | k ≤ (univ.filter fun j => X j ω < X i₀ ω).card}
      ≤ ((Fintype.card ι - k : ℕ) : ℝ≥0∞) / Fintype.card ι := by
  set N := Fintype.card ι with hN
  set Ev : ι → Set Ω := fun i => {ω | k ≤ (univ.filter fun j => X j ω < X i ω).card} with hEv
  have hXm : Measurable fun ω l => X l ω := measurable_pi_iff.mpr hmeas
  have hEvm : ∀ i, MeasurableSet (Ev i) := fun i => hXm (measurableSet_le_card_lt k i)
  have hNpos : 0 < N := Fintype.card_pos_iff.mpr ⟨i₀⟩
  -- the indicators of the events sum to at most `N - k` pointwise
  have hpt : ∀ ω, ∑ i, (Ev i).indicator (fun _ => (1 : ℝ≥0∞)) ω ≤ ((N - k : ℕ) : ℝ≥0∞) := by
    intro ω
    classical
    have h1 : ∑ i, (Ev i).indicator (fun _ => (1 : ℝ≥0∞)) ω
        = ((univ.filter fun i => k ≤ (univ.filter fun j => X j ω < X i ω).card).card : ℝ≥0∞) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : k ≤ (univ.filter fun j => X j ω < X i ω).card
      · rw [Set.indicator_of_mem (by exact h)]; simp [h]
      · rw [Set.indicator_of_notMem (by exact h)]; simp [h]
    rw [h1]
    exact_mod_cast card_filter_le_card_lt_le' (fun j => X j ω) k
  have hsum : (N : ℝ≥0∞) * P (Ev i₀) ≤ ((N - k : ℕ) : ℝ≥0∞) := by
    calc (N : ℝ≥0∞) * P (Ev i₀) = ∑ i : ι, P (Ev i) := by
          rw [Finset.sum_congr rfl fun i _ => hX.measure_le_card_lt_eq hmeas k i i₀,
            Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ∫⁻ ω, ∑ i, (Ev i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
          rw [lintegral_finsetSum _ fun i _ => measurable_const.indicator (hEvm i)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_indicator_const (hEvm i), one_mul]
      _ ≤ ∫⁻ _ω, ((N - k : ℕ) : ℝ≥0∞) ∂P := lintegral_mono hpt
      _ = ((N - k : ℕ) : ℝ≥0∞) := by simp
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hNpos.ne'))
    (Or.inl (ENNReal.natCast_ne_top N)), mul_comm]
  exact hsum

/-- **Split conformal prediction: finite-sample coverage.** Let `N = n + 1` scores (the `n`
calibration scores and the test score, indexed by `ι`) be exchangeable, and let
`k ≥ (1 - α) N`. The test score exceeds the `k`-th smallest calibration score exactly when at
least `k` of the other scores lie strictly below it, and this happens with probability at
most `α`. Equivalently, the conformal prediction set covers with probability at least
`1 - α`. -/
theorem conformal_miscoverage_le {P : Measure Ω} [IsProbabilityMeasure P]
    {S : ι → Ω → ℝ} (hS : Exchangeable P S) (hmeas : ∀ i, Measurable (S i)) (test : ι)
    (α : ℝ) (k : ℕ) (hk : (1 - α) * Fintype.card ι ≤ k) :
    P {ω | k ≤ (univ.filter fun j => S j ω < S test ω).card} ≤ ENNReal.ofReal α := by
  refine (hS.measure_le_card_lt_le hmeas k test).trans ?_
  have hNpos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨test⟩
  rw [ENNReal.div_le_iff (by exact_mod_cast hNpos.ne') (ENNReal.natCast_ne_top _),
    ← ENNReal.ofReal_natCast (Fintype.card ι), ← ENNReal.ofReal_mul' (Nat.cast_nonneg _),
    ← ENNReal.ofReal_natCast (Fintype.card ι - k)]
  rcases le_or_gt k (Fintype.card ι) with hle | hgt
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [Nat.cast_sub hle]; nlinarith
  · rw [Nat.sub_eq_zero_of_le hgt.le]; simp

end Main

end Applied.Conformal
