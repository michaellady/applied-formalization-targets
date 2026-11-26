import Applied.Statistics.BenjaminiHochberg

/-!
# Benjamini–Yekutieli: false discovery rate under arbitrary dependence

With no assumption on the dependence between p-values, the Benjamini–Hochberg procedure at
level `α` has false discovery rate at most `α (m₀ / m) (1 + 1/2 + ⋯ + 1/m)`.

* `byConst m`: the harmonic number `1 + 1/2 + ⋯ + 1/m` (`byConst_eq_harmonic`).
* `fdr_bhReject_le_of_arbitrary_dependence`: the **Benjamini–Yekutieli theorem** (2001,
  Theorem 1.3). The only hypotheses are `α ≥ 0`, measurability, and validity of the true-null
  p-values. Equivalently, running Benjamini–Hochberg at level `α / byConst m` controls the
  false discovery rate at `α m₀ / m` under any dependence.

The proof bounds each true null's contribution `1 / |R|` by a function of its own p-value
alone (`fdp_bhReject_le_bands`), using `1 / k = ∑_{k ≤ j < m} 1 / (j (j + 1)) + 1 / m`
(`sum_Ico_inv_mul_succ`, `one_div_le_sum_bands`).

Related: `BenjaminiHochberg` (independence, no harmonic factor), `PRDS` (positive dependence, no
harmonic factor), `SimesSharp` (the harmonic factor is attained for the Simes test).
Not here: sharpness of the bound for the false discovery rate when some nulls are false.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

/-- Telescoping sum `∑_{k ≤ j < m} 1 / (j (j + 1)) = 1 / k - 1 / m`. -/
lemma sum_Ico_inv_mul_succ {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    ∑ j ∈ Ico k m, (1 : ℝ) / ((j : ℝ) * (j + 1)) = 1 / k - 1 / m := by
  induction m, hkm using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [Finset.sum_Ico_succ_top hkn, ih]
    have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk hkn)
    push_cast
    field_simp
    ring

/-- If `x` is below the `k`-th of an increasing sequence of thresholds, then `1 / k` is at most
a weighted count of the thresholds that `x` is below. -/
lemma one_div_le_sum_bands {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (t : ℕ → ℝ) (ht : Monotone t)
    (x : ℝ) (hx : x ≤ t k) :
    (1 : ℝ) / k ≤ ∑ j ∈ Ico 1 m, (if x ≤ t j then (1 : ℝ) / ((j : ℝ) * (j + 1)) else 0)
      + (if x ≤ t m then (1 : ℝ) / m else 0) := by
  have hlast : (if x ≤ t m then (1 : ℝ) / m else 0) = 1 / m := by
    simp [hx.trans (ht hkm)]
  have hsub : ∑ j ∈ Ico k m, (1 : ℝ) / ((j : ℝ) * (j + 1))
      ≤ ∑ j ∈ Ico 1 m, (if x ≤ t j then (1 : ℝ) / ((j : ℝ) * (j + 1)) else 0) := by
    have h1 : ∑ j ∈ Ico k m, (1 : ℝ) / ((j : ℝ) * (j + 1))
        = ∑ j ∈ Ico k m, (if x ≤ t j then (1 : ℝ) / ((j : ℝ) * (j + 1)) else 0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [hx.trans (ht (mem_Ico.mp hj).1)]
    rw [h1]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left hk) fun j _ _ => ?_
    split_ifs
    · positivity
    · exact le_rfl
  rw [hlast]
  have := sum_Ico_inv_mul_succ hk hkm
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ}

/-- The Benjamini–Yekutieli constant: `1 + ∑_{1 ≤ j < m} 1 / (j + 1)`, which equals
the harmonic number `1 + 1/2 + ⋯ + 1/m` for `m ≥ 1`. -/
noncomputable def byConst (m : ℕ) : ℝ := ∑ j ∈ Ico 1 m, (1 : ℝ) / (j + 1) + 1

/-- For `m ≥ 1`, `byConst m` is the harmonic number `H_m = 1 + 1/2 + ⋯ + 1/m`. -/
lemma byConst_eq_harmonic {m : ℕ} (hm : 1 ≤ m) :
    byConst m = ∑ j ∈ range m, (1 : ℝ) / (j + 1) := by
  induction m, hm using Nat.le_induction with
  | base => simp [byConst]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ← ih, byConst, byConst, Finset.sum_Ico_succ_top hn]
    ring

/-- Pointwise bound on the false discovery proportion in terms of each true null's own
p-value. -/
theorem fdp_bhReject_le_bands (hα : 0 ≤ α) (H₀ : Finset ι) (q : ι → ℝ) :
    fdp H₀ (bhReject α q) ≤ ∑ i ∈ H₀,
      (∑ j ∈ Ico 1 (Fintype.card ι),
          (if q i ≤ α * j / Fintype.card ι then ENNReal.ofReal (1 / ((j : ℝ) * (j + 1))) else 0)
        + (if q i ≤ α * (Fintype.card ι : ℕ) / Fintype.card ι
            then ENNReal.ofReal (1 / (Fintype.card ι : ℝ)) else 0)) := by
  classical
  set m := Fintype.card ι with hm
  have hcard : ((bhReject α q ∩ H₀).card : ℝ≥0∞)
      = ∑ i ∈ H₀, if i ∈ bhReject α q then (1 : ℝ≥0∞) else 0 := by
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    push_cast
    rfl
  rw [fdp, hcard, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ bhReject α q
  · simp only [hi, ↓reduceIte, one_mul]
    set k := bhK α q with hk
    have hk1 : 1 ≤ k := one_le_bhK hα q hi
    have hkm : k ≤ m := bhK_le q
    have hmono : Monotone fun j : ℕ => α * j / m := by
      intro a b hab
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      simp only
      gcongr
    have hreal := one_div_le_sum_bands hk1 hkm (fun j : ℕ => α * j / m) hmono (q i)
      (mem_filter.mp hi).2
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    calc ((bhReject α q).card : ℝ≥0∞)⁻¹ ≤ ((k : ℝ≥0∞))⁻¹ := by
          rw [ENNReal.inv_le_inv]; exact_mod_cast bhK_le_card_bhReject q
      _ = ENNReal.ofReal (1 / k) := by
          rw [one_div, ENNReal.ofReal_inv_of_pos hkpos, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (∑ j ∈ Ico 1 m,
            (if q i ≤ α * j / m then (1 : ℝ) / ((j : ℝ) * (j + 1)) else 0)
            + (if q i ≤ α * (m : ℕ) / m then (1 : ℝ) / m else 0)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
          rw [ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => by split_ifs <;> positivity)
            (by split_ifs <;> positivity),
            ENNReal.ofReal_sum_of_nonneg fun j _ => by split_ifs <;> positivity]
          congr 1
          · refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs <;> simp
          · split_ifs <;> simp
  · simp only [hi, ↓reduceIte, zero_mul]; exact zero_le

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Benjamini–Yekutieli theorem.** Under arbitrary dependence, the Benjamini–Hochberg
procedure at level `α` has false discovery rate at most `α (m₀ / m) (1 + 1/2 + ⋯ + 1/m)`. -/
theorem fdr_bhReject_le_of_arbitrary_dependence (P : Measure Ω) (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι * byConst (Fintype.card ι)) := by
  set m := Fintype.card ι with hm
  -- integral of one indicator term
  have hind : ∀ i ∈ H₀, ∀ (t : ℝ) (c : ℝ≥0∞), 0 ≤ t →
      ∫⁻ ω, (if p i ω ≤ t then c else 0) ∂P ≤ c * ENNReal.ofReal t := by
    intro i hi t c ht
    have hfun : (fun ω => if p i ω ≤ t then c else 0)
        = (p i ⁻¹' Set.Iic t).indicator fun _ => c := by
      funext ω
      by_cases h : p i ω ≤ t
      · rw [Set.indicator_of_mem (by exact h)]; simp [h]
      · rw [Set.indicator_of_notMem (by exact h)]; simp [h]
    rw [hfun, lintegral_indicator_const (hmeas i measurableSet_Iic)]
    gcongr
    exact hvalid i hi t ht
  have hmeasT : ∀ i (t : ℝ) (c : ℝ≥0∞), Measurable fun ω => if p i ω ≤ t then c else 0 :=
    fun i t c => Measurable.ite (hmeas i measurableSet_Iic) measurable_const measurable_const
  -- contribution of a single true null
  have hone : ∀ i ∈ H₀,
      ∫⁻ ω, (∑ j ∈ Ico 1 m,
          (if p i ω ≤ α * j / m then ENNReal.ofReal (1 / ((j : ℝ) * (j + 1))) else 0)
        + (if p i ω ≤ α * (m : ℕ) / m then ENNReal.ofReal (1 / (m : ℝ)) else 0)) ∂P
      ≤ ENNReal.ofReal (α / m * byConst m) := by
    intro i hi
    rw [lintegral_add_left (Finset.measurable_sum _ fun j _ => hmeasT i _ _),
      lintegral_finsetSum _ fun j _ => hmeasT i _ _]
    have h1 : ∑ j ∈ Ico 1 m, ∫⁻ ω,
        (if p i ω ≤ α * j / m then ENNReal.ofReal (1 / ((j : ℝ) * (j + 1))) else 0) ∂P
        ≤ ∑ j ∈ Ico 1 m, ENNReal.ofReal (α / m * (1 / ((j : ℝ) + 1))) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj1 : (0 : ℝ) < j := by exact_mod_cast (mem_Ico.mp hj).1
      refine (hind i hi _ _ (by positivity)).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      field_simp
    have h2 : ∫⁻ ω, (if p i ω ≤ α * (m : ℕ) / m then ENNReal.ofReal (1 / (m : ℝ)) else 0) ∂P
        ≤ ENNReal.ofReal (α / m) := by
      refine (hind i hi _ _ (by positivity)).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · simp [h0]
      · have : (0 : ℝ) < m := by exact_mod_cast hpos
        apply le_of_eq; field_simp
    calc _ ≤ ∑ j ∈ Ico 1 m, ENNReal.ofReal (α / m * (1 / ((j : ℝ) + 1)))
          + ENNReal.ofReal (α / m) := add_le_add h1 h2
      _ = ENNReal.ofReal (α / m * byConst m) := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity,
            ← ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => by positivity) (by positivity)]
          congr 1
          rw [byConst, ← Finset.mul_sum]; ring
  calc fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ∫⁻ ω, ∑ i ∈ H₀, (∑ j ∈ Ico 1 m,
          (if p i ω ≤ α * j / m then ENNReal.ofReal (1 / ((j : ℝ) * (j + 1))) else 0)
        + (if p i ω ≤ α * (m : ℕ) / m then ENNReal.ofReal (1 / (m : ℝ)) else 0)) ∂P :=
        lintegral_mono fun ω => fdp_bhReject_le_bands hα H₀ _
    _ = ∑ i ∈ H₀, ∫⁻ ω, (∑ j ∈ Ico 1 m,
          (if p i ω ≤ α * j / m then ENNReal.ofReal (1 / ((j : ℝ) * (j + 1))) else 0)
        + (if p i ω ≤ α * (m : ℕ) / m then ENNReal.ofReal (1 / (m : ℝ)) else 0)) ∂P :=
        lintegral_finsetSum _ fun i _ =>
          (Finset.measurable_sum _ fun j _ => hmeasT i _ _).add (hmeasT i _ _)
    _ ≤ ∑ _i ∈ H₀, ENNReal.ofReal (α / m * byConst m) := Finset.sum_le_sum hone
    _ = ENNReal.ofReal (α * H₀.card / m * byConst m) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast H₀.card,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1; ring

end Applied.MultipleTesting
