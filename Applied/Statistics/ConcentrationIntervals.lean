import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.IdentDistrib

/-!
# Confidence intervals for a mean from concentration inequalities

For random variables `X 0, …, X (n-1)` with common mean `m`, the sample mean is
`(∑ i < n, X i) / n`.

* **Chebyshev.** If the `X i` are square integrable, pairwise independent, and have common
  variance `v`, then `P(|mean - m| ≥ ε) ≤ v / (n ε²)`, and the interval
  `mean ± √(v / (n α))` covers `m` with probability at least `1 - α`.
* **Hoeffding.** If the `X i` are mutually independent and almost surely in `[a, b]`, then
  `P(|mean - m| ≥ ε) ≤ 2 exp (-2 n ε² / (b - a)²)`, and the interval
  `mean ± (b - a) √(log (2 / α) / (2 n))` covers `m` with probability at least `1 - α`.

The variables are not required to be identically distributed: only the common mean (and, for
Chebyshev, the common variance) is used. Versions for identically distributed variables are
given as corollaries.

## Relation to other files and scope

Stand-alone (Mathlib only). `SimultaneousIntervals.lean` turns several such intervals into a
simultaneous statement by Bonferroni. Probabilities are real numbers (`Measure.real`). Not
here: variables with different ranges `[aᵢ, bᵢ]`, estimated variance (t-intervals),
Bernstein-type intervals, and exact (Clopper–Pearson) or asymptotic normal intervals.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Applied.Statistics

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The sample mean of `X 0, …, X (n-1)`. -/
noncomputable def sampleMean (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ range n, X i ω) / n

section Chebyshev

variable [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {n : ℕ} {m v : ℝ}

/-- **Chebyshev bound for the sample mean**, as a measure in `ℝ≥0∞`. -/
theorem measure_le_abs_sampleMean_sub_le_ofReal (hn : 0 < n)
    (hX : ∀ i < n, MemLp (X i) 2 P)
    (hindep : Set.Pairwise (range n : Set ℕ) fun i j => X i ⟂ᵢ[P] X j)
    (hmean : ∀ i < n, P[X i] = m) (hvar : ∀ i < n, Var[X i; P] = v) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |sampleMean X n ω - m|} ≤ ENNReal.ofReal (v / (n * ε ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hX' : ∀ i ∈ range n, MemLp (X i) 2 P := fun i hi => hX i (mem_range.mp hi)
  have hS : MemLp (∑ i ∈ range n, X i) 2 P := memLp_finsetSum' _ hX'
  have hES : P[∑ i ∈ range n, X i] = n * m := by
    have : ∀ ω, (∑ i ∈ range n, X i) ω = ∑ i ∈ range n, X i ω := fun ω => by simp
    simp_rw [this]
    rw [integral_finsetSum _ fun i hi => (hX' i hi).integrable one_le_two,
      sum_congr rfl fun i hi => hmean i (mem_range.mp hi)]
    simp
  have hVS : Var[∑ i ∈ range n, X i; P] = n * v := by
    rw [IndepFun.variance_sum hX' hindep, sum_congr rfl fun i hi => hvar i (mem_range.mp hi)]
    simp
  have key := meas_ge_le_variance_div_sq hS (mul_pos hn' hε)
  rw [hES, hVS] at key
  have hset : {ω | ε ≤ |sampleMean X n ω - m|}
      = {ω | n * ε ≤ |(∑ i ∈ range n, X i) ω - n * m|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, sampleMean]
    have : (∑ i ∈ range n, X i ω) - n * m = n * ((∑ i ∈ range n, X i ω) / n - m) := by
      field_simp
    rw [Finset.sum_apply, this, abs_mul, abs_of_pos hn', mul_le_mul_iff_right₀ hn']
  rw [hset]
  refine key.trans_eq ?_
  congr 1
  field_simp

/-- **Chebyshev bound for the sample mean**:
`P(|mean - m| ≥ ε) ≤ v / (n ε²)` for pairwise independent square-integrable variables with
common mean `m` and common variance `v`. -/
theorem measureReal_le_abs_sampleMean_sub_le (hn : 0 < n)
    (hX : ∀ i < n, MemLp (X i) 2 P)
    (hindep : Set.Pairwise (range n : Set ℕ) fun i j => X i ⟂ᵢ[P] X j)
    (hmean : ∀ i < n, P[X i] = m) (hvar : ∀ i < n, Var[X i; P] = v) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |sampleMean X n ω - m|} ≤ v / (n * ε ^ 2) := by
  have hv : 0 ≤ v := by rw [← hvar 0 hn]; exact variance_nonneg _ _
  have h := measure_le_abs_sampleMean_sub_le_ofReal hn hX hindep hmean hvar hε
  have h0 : 0 ≤ v / (n * ε ^ 2) := by positivity
  exact (ENNReal.toReal_le_of_le_ofReal h0 h)

/-- **Chebyshev confidence interval**: the interval `mean ± √(v / (n α))` (that is,
`mean ± σ / √(n α)` with `σ = √v`) covers the common mean `m` with probability at least
`1 - α`. -/
theorem one_sub_le_measureReal_abs_sampleMean_sub_le_sqrt (hn : 0 < n)
    (hX : ∀ i < n, MemLp (X i) 2 P)
    (hindep : Set.Pairwise (range n : Set ℕ) fun i j => X i ⟂ᵢ[P] X j)
    (hmean : ∀ i < n, P[X i] = m) (hvar : ∀ i < n, Var[X i; P] = v) {α : ℝ} (hα : 0 < α) :
    1 - α ≤ P.real {ω | |sampleMean X n ω - m| ≤ √(v / (n * α))} := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : 0 ≤ v := by rw [← hvar 0 hn]; exact variance_nonneg _ _
  set w := √(v / (n * α)) with hw
  have hmeas : NullMeasurableSet {ω | |sampleMean X n ω - m| ≤ w} P := by
    have hS : AEMeasurable (fun ω => |sampleMean X n ω - m|) P := by
      have : AEMeasurable (fun ω => ∑ i ∈ range n, X i ω) P :=
        Finset.aemeasurable_fun_sum _ fun i hi => (hX i (mem_range.mp hi)).aemeasurable
      unfold sampleMean
      fun_prop
    exact nullMeasurableSet_le hS aemeasurable_const
  have hcompl : P.real {ω | |sampleMean X n ω - m| ≤ w}ᶜ ≤ α := by
    have hc : {ω | |sampleMean X n ω - m| ≤ w}ᶜ = {ω | w < |sampleMean X n ω - m|} := by
      ext ω; simp
    rw [hc]
    rcases hv.eq_or_lt with hv0 | hv0
    · -- zero variance: the sample mean equals `m` almost surely
      have hw0 : w = 0 := by rw [hw, ← hv0]; simp
      have hnull : P {ω | w < |sampleMean X n ω - m|} = 0 := by
        have hsub : {ω | w < |sampleMean X n ω - m|}
            ⊆ ⋃ k : ℕ, {ω | 1 / ((k : ℝ) + 1) ≤ |sampleMean X n ω - m|} := by
          intro ω hω
          rw [Set.mem_ofPred_eq, hw0] at hω
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt hω
          exact Set.mem_iUnion.mpr ⟨k, show _ ≤ _ from hk.le⟩
        refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
        have h := measure_le_abs_sampleMean_sub_le_ofReal hn hX hindep hmean hvar
          (ε := 1 / ((k : ℝ) + 1)) (by positivity)
        rw [← hv0] at h
        simpa using h
      rw [measureReal_def, hnull]
      simpa using hα.le
    · have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
      calc P.real {ω | w < |sampleMean X n ω - m|}
          ≤ P.real {ω | w ≤ |sampleMean X n ω - m|} :=
            measureReal_mono fun ω (hω : w < _) => show w ≤ _ from hω.le
        _ ≤ v / (n * w ^ 2) :=
            measureReal_le_abs_sampleMean_sub_le hn hX hindep hmean hvar hwpos
        _ = α := by
            rw [hw, Real.sq_sqrt (by positivity)]
            field_simp
  have := measureReal_compl₀ (μ := P) hmeas
  rw [probReal_univ] at this
  linarith

/-- Chebyshev bound for the sample mean of pairwise independent, identically distributed,
square-integrable variables. -/
theorem measureReal_le_abs_sampleMean_sub_le_of_identDistrib (hn : 0 < n)
    (hX : MemLp (X 0) 2 P) (hindep : Pairwise fun i j => X i ⟂ᵢ[P] X j)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |sampleMean X n ω - P[X 0]|} ≤ Var[X 0; P] / (n * ε ^ 2) :=
  measureReal_le_abs_sampleMean_sub_le hn (fun i _ => (hident i).symm.memLp_snd hX)
    (fun _ _ _ _ hij => hindep hij) (fun i _ => (hident i).integral_eq)
    (fun i _ => (hident i).variance_eq) hε

/-- Chebyshev confidence interval for pairwise independent, identically distributed,
square-integrable variables. -/
theorem one_sub_le_measureReal_abs_sampleMean_sub_le_sqrt_of_identDistrib (hn : 0 < n)
    (hX : MemLp (X 0) 2 P) (hindep : Pairwise fun i j => X i ⟂ᵢ[P] X j)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α) :
    1 - α ≤ P.real {ω | |sampleMean X n ω - P[X 0]| ≤ √(Var[X 0; P] / (n * α))} :=
  one_sub_le_measureReal_abs_sampleMean_sub_le_sqrt hn (fun i _ => (hident i).symm.memLp_snd hX)
    (fun _ _ _ _ hij => hindep hij) (fun i _ => (hident i).integral_eq)
    (fun i _ => (hident i).variance_eq) hα

end Chebyshev

section Hoeffding

variable [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {n : ℕ} {m a b : ℝ}

/-- **Hoeffding bound for the sample mean, upper tail.** -/
theorem measureReal_le_sampleMean_sub_le_exp (hn : 0 < n) (hindep : iIndepFun X P)
    (hXm : ∀ i < n, AEMeasurable (X i) P) (hab : ∀ i < n, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc a b)
    (hmean : ∀ i < n, P[X i] = m) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ sampleMean X n ω - m} ≤ Real.exp (-2 * n * ε ^ 2 / (b - a) ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : a ≤ b := by
    obtain ⟨ω, hω⟩ := (hab 0 hn).exists
    exact hω.1.trans hω.2
  have hindep' : iIndepFun (fun i ω => X i ω - P[X i]) P :=
    hindep.comp (β := fun _ => ℝ) (γ := fun _ => ℝ) (fun i x => x - ∫ ω, X i ω ∂P)
      (fun i => by fun_prop)
  have hsub : ∀ i < n,
      HasSubgaussianMGF (fun ω => X i ω - P[X i]) ((‖b - a‖₊ / 2) ^ 2) P :=
    fun i hi => hasSubgaussianMGF_of_mem_Icc (hXm i hi) (hab i hi)
  have hnε : 0 ≤ n * ε := by positivity
  have key : P.real {ω | n * ε ≤ ∑ i ∈ range n, (X i ω - P[X i])}
      ≤ Real.exp (-(n * ε) ^ 2 / (2 * n * ((‖b - a‖₊ / 2) ^ 2 : ℝ≥0))) :=
    HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindep' hsub hnε
  have hset : {ω | ε ≤ sampleMean X n ω - m}
      = {ω | n * ε ≤ ∑ i ∈ range n, (X i ω - P[X i])} := by
    ext ω
    simp only [Set.mem_ofPred_eq, sampleMean]
    rw [sum_sub_distrib, sum_congr rfl fun i hi => hmean i (mem_range.mp hi)]
    have : (∑ i ∈ range n, X i ω) - ∑ _i ∈ range n, m
        = n * ((∑ i ∈ range n, X i ω) / n - m) := by
      simp; field_simp
    rw [this, mul_le_mul_iff_right₀ hn']
  rw [hset]
  refine key.trans_eq ?_
  congr 1
  have hnorm : ‖b - a‖ = b - a := Real.norm_of_nonneg (sub_nonneg.mpr hle)
  push_cast
  rw [hnorm]
  rcases eq_or_ne (b - a) 0 with h0 | h0
  · simp [h0]
  · field_simp

/-- **Hoeffding bound for the sample mean, lower tail.** -/
theorem measureReal_le_sub_sampleMean_le_exp (hn : 0 < n) (hindep : iIndepFun X P)
    (hXm : ∀ i < n, AEMeasurable (X i) P) (hab : ∀ i < n, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc a b)
    (hmean : ∀ i < n, P[X i] = m) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ m - sampleMean X n ω} ≤ Real.exp (-2 * n * ε ^ 2 / (b - a) ^ 2) := by
  have hindep' : iIndepFun (fun i ω => -X i ω) P :=
    hindep.comp (fun _ x => -x) (fun _ => measurable_neg)
  have key := measureReal_le_sampleMean_sub_le_exp (X := fun i ω => -X i ω) (m := -m)
    (a := -b) (b := -a) hn hindep' (fun i hi => (hXm i hi).neg)
    (fun i hi => by
      filter_upwards [hab i hi] with ω hω
      exact ⟨neg_le_neg hω.2, neg_le_neg hω.1⟩)
    (fun i hi => by rw [integral_neg, hmean i hi]) hε
  have hset : {ω | ε ≤ m - sampleMean X n ω}
      = {ω | ε ≤ sampleMean (fun i ω => -X i ω) n ω - -m} := by
    ext ω
    simp only [Set.mem_ofPred_eq, sampleMean, sum_neg_distrib]
    rw [neg_div]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine key.trans_eq ?_
  congr 2
  ring

/-- **Hoeffding bound for the sample mean, two-sided**:
`P(|mean - m| ≥ ε) ≤ 2 exp (-2 n ε² / (b - a)²)` for independent variables in `[a, b]` with
common mean `m`. -/
theorem measureReal_le_abs_sampleMean_sub_le_two_mul_exp (hn : 0 < n) (hindep : iIndepFun X P)
    (hXm : ∀ i < n, AEMeasurable (X i) P) (hab : ∀ i < n, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc a b)
    (hmean : ∀ i < n, P[X i] = m) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |sampleMean X n ω - m|}
      ≤ 2 * Real.exp (-2 * n * ε ^ 2 / (b - a) ^ 2) := by
  have hsub : {ω | ε ≤ |sampleMean X n ω - m|}
      ⊆ {ω | ε ≤ sampleMean X n ω - m} ∪ {ω | ε ≤ m - sampleMean X n ω} := by
    intro ω (hω : ε ≤ |sampleMean X n ω - m|)
    rcases le_abs'.mp hω with h | h
    · exact Or.inr (by simp only [Set.mem_ofPred_eq]; linarith)
    · exact Or.inl h
  calc P.real {ω | ε ≤ |sampleMean X n ω - m|}
      ≤ P.real ({ω | ε ≤ sampleMean X n ω - m} ∪ {ω | ε ≤ m - sampleMean X n ω}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | ε ≤ sampleMean X n ω - m} + P.real {ω | ε ≤ m - sampleMean X n ω} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-2 * n * ε ^ 2 / (b - a) ^ 2) := by
        have h1 := measureReal_le_sampleMean_sub_le_exp hn hindep hXm hab hmean hε
        have h2 := measureReal_le_sub_sampleMean_le_exp hn hindep hXm hab hmean hε
        linarith

/-- Coverage of the open interval `mean ± ε`: it contains the common mean with probability at
least `1 - 2 exp (-2 n ε² / (b - a)²)`. -/
theorem one_sub_two_mul_exp_le_measureReal_abs_sampleMean_sub_lt (hn : 0 < n)
    (hindep : iIndepFun X P)
    (hXm : ∀ i < n, AEMeasurable (X i) P) (hab : ∀ i < n, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc a b)
    (hmean : ∀ i < n, P[X i] = m) {ε : ℝ} (hε : 0 ≤ ε) :
    1 - 2 * Real.exp (-2 * n * ε ^ 2 / (b - a) ^ 2)
      ≤ P.real {ω | |sampleMean X n ω - m| < ε} := by
  have hmeas : NullMeasurableSet {ω | |sampleMean X n ω - m| < ε} P := by
    have hS : AEMeasurable (fun ω => |sampleMean X n ω - m|) P := by
      have : AEMeasurable (fun ω => ∑ i ∈ range n, X i ω) P :=
        Finset.aemeasurable_fun_sum _ fun i hi => hXm i (mem_range.mp hi)
      unfold sampleMean
      fun_prop
    exact nullMeasurableSet_lt hS aemeasurable_const
  have hc : {ω | |sampleMean X n ω - m| < ε}ᶜ = {ω | ε ≤ |sampleMean X n ω - m|} := by
    ext ω; simp
  have h1 := measureReal_compl₀ (μ := P) hmeas
  rw [probReal_univ, hc] at h1
  have h2 := measureReal_le_abs_sampleMean_sub_le_two_mul_exp hn hindep hXm hab hmean hε
  linarith

/-- **Hoeffding confidence interval**: for `a < b` and `0 < α`, the open interval
`mean ± (b - a) √(log (2 / α) / (2 n))` covers the common mean `m` with probability at least
`1 - α`. -/
theorem one_sub_le_measureReal_abs_sampleMean_sub_lt_hoeffding (hn : 0 < n)
    (hindep : iIndepFun X P)
    (hXm : ∀ i < n, AEMeasurable (X i) P) (hab : ∀ i < n, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc a b)
    (hmean : ∀ i < n, P[X i] = m) (hlt : a < b) {α : ℝ} (hα : 0 < α) :
    1 - α ≤ P.real {ω | |sampleMean X n ω - m| < (b - a) * √(Real.log (2 / α) / (2 * n))} := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases le_or_gt α 2 with hα2 | hα2
  · have hlog : 0 ≤ Real.log (2 / α) := Real.log_nonneg (by rw [le_div_iff₀ hα]; linarith)
    have hba : 0 < b - a := sub_pos.mpr hlt
    set ε := (b - a) * √(Real.log (2 / α) / (2 * n)) with hε
    have hε0 : 0 ≤ ε := by positivity
    have h := one_sub_two_mul_exp_le_measureReal_abs_sampleMean_sub_lt hn hindep hXm hab hmean hε0
    have hexp : 2 * Real.exp (-2 * n * ε ^ 2 / (b - a) ^ 2) = α := by
      have : -2 * n * ε ^ 2 / (b - a) ^ 2 = -Real.log (2 / α) := by
        rw [hε, mul_pow, Real.sq_sqrt (by positivity)]
        field_simp
      rw [this, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    linarith
  · exact le_trans (by linarith) measureReal_nonneg

end Hoeffding

end Applied.Statistics
