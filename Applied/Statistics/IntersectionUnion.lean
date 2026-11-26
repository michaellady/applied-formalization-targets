import Applied.Statistics.CombinedPValues
import Applied.Statistics.ClosedTesting
import Applied.Statistics.StandardNormal
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

/-!
# Intersection-union tests: TOST, co-primary endpoints, non-inferiority then superiority

An intersection-union test rejects a union null hypothesis `H₀ = ⋃ᵢ H₀ᵢ` when every component
test rejects. No multiplicity adjustment is needed.

General part (arbitrary index type, arbitrary family of measures, no measurability):

* `iut_level`: if each `R i` has level `α` for `H₀ i`, then `⋂ᵢ R i` has level `α` for
  `⋃ᵢ H₀ i` (Berger 1982).
* `iut_size_eq`, `iut_size_eq_of_measurable`: Berger's sufficient condition for the size to be
  exactly `α` (finite index type).
* `one_le_measure_iInter_add_sum_compl`, `coprimary_power_ge`: the power of "all endpoints
  significant" is at least one minus the sum of the type II errors, under any dependence.
* `measure_false_claim_le`, `ni_then_superiority_fwer_le`: all claims `θ > t` read off one
  lower confidence bound are simultaneously correct with the coverage probability of the bound;
  in particular non-inferiority and superiority can both be tested at full level.
* `fwer_nested_two_le`: the same for two p-values with nested rejections, from
  `fwer_fixedSequence_le`.

Normal mean with known standard error `s` (the estimate has law `N(θ, s²)` on the real line;
`Φ` is the standard normal cdf, the critical value `c` is arbitrary (`c ≥ 0` for the
confidence-interval form) and the one-sided level is
`1 - Φ c`):

* `zTest_upper_level`, `zTest_lower_level`: the one-sided z-tests have level `1 - Φ c`.
* `tostRegion`, `mem_tostRegion_iff_ci`: the two one-sided tests both reject iff the interval
  `[x - c s, x + c s]` lies inside `(-δ, δ)`; `ci_coverage`: that interval has coverage
  `1 - 2 (1 - Φ c)`.
* `tost_prob`, `tost_prob_at_margin`: closed-form rejection probability.
* `tost_level`: level `1 - Φ c` on `|θ| ≥ δ`; `tost_prob_le_margin`, `tost_size`,
  `tost_size_lt`: for `c ≥ 0` the size is `max 0 ((1 - Φ c) - Φ (c - 2 δ / s))`, attained at
  `θ = ±δ` and strictly below `1 - Φ c`.
* `ni_then_superiority_gaussian`: non-inferiority then superiority with the bound `x - c s`.

The p-value form of `iut_level` is `Applied.MultipleTesting.isValidPValue_iSup_of_isValidPValue`
(the maximum p-value).

## Relation to other files and scope

`CombinedPValues.lean` has the maximum p-value; `ClosedTesting.lean` the fixed-sequence test;
`StandardNormal.lean` the facts about `Φ` (re-exported here under their old names). Not here:
the t-test (unknown variance) TOST, ratio-scale bioequivalence limits (80–125%), asymmetric
margins, and more powerful equivalence tests (Berger–Hsu).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Applied.IntersectionUnion

/-! ### The intersection-union theorem -/

section General

variable {Ω Θ ι : Type*} [MeasurableSpace Ω]

/-- **Intersection-union theorem** (Berger 1982). If for every `i` the region `R i` has
probability at most `α` under every parameter in `H₀ i`, then the intersection of all regions
has probability at most `α` under every parameter in the union of the `H₀ i`. Any index type,
any dependence, no measurability. -/
theorem iut_level (P : Θ → Measure Ω) (H₀ : ι → Set Θ) (R : ι → Set Ω) (α : ℝ≥0∞)
    (hR : ∀ i, ∀ θ ∈ H₀ i, P θ (R i) ≤ α) {θ : Θ} (hθ : θ ∈ ⋃ i, H₀ i) :
    P θ (⋂ i, R i) ≤ α := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hθ
  exact (measure_mono (iInter_subset _ i)).trans (hR i θ hi)

/-- The probability of one region is at most the probability of the intersection plus the
probabilities that the other regions fail. -/
theorem measure_le_iInter_add_sum_compl [Fintype ι] [DecidableEq ι] (μ : Measure Ω)
    (R : ι → Set Ω) (i : ι) :
    μ (R i) ≤ μ (⋂ j, R j) + ∑ j ∈ Finset.univ.erase i, μ (R j)ᶜ := by
  have hsub : R i ⊆ (⋂ j, R j) ∪ ⋃ j ∈ Finset.univ.erase i, (R j)ᶜ := by
    intro ω hω
    by_cases h : ∀ j, ω ∈ R j
    · exact Or.inl (mem_iInter.mpr h)
    · push Not at h
      obtain ⟨j, hj⟩ := h
      refine Or.inr (mem_iUnion₂.mpr ⟨j, ?_, hj⟩)
      rw [Finset.mem_erase]
      exact ⟨fun h => hj (h ▸ hω), Finset.mem_univ _⟩
  calc μ (R i) ≤ μ ((⋂ j, R j) ∪ ⋃ j ∈ Finset.univ.erase i, (R j)ᶜ) := measure_mono hsub
    _ ≤ μ (⋂ j, R j) + μ (⋃ j ∈ Finset.univ.erase i, (R j)ᶜ) := measure_union_le _ _
    _ ≤ μ (⋂ j, R j) + ∑ j ∈ Finset.univ.erase i, μ (R j)ᶜ := by
        gcongr
        exact measure_biUnion_finset_le _ _

/-- **Exact size of an intersection-union test** (Berger's sufficient condition). In addition
to the level condition of `iut_level`, suppose there is an index `i` and a sequence of
parameters in `H₀ i` along which the probability of `R i` tends to `α` and, for every other
`j`, the probability of the complement of `R j` tends to `0`. Then the supremum of the
rejection probability over the union null is exactly `α`. Finite index type. -/
theorem iut_size_eq [Fintype ι] (P : Θ → Measure Ω) (H₀ : ι → Set Θ) (R : ι → Set Ω)
    (α : ℝ≥0∞) (hR : ∀ i, ∀ θ ∈ H₀ i, P θ (R i) ≤ α) (i : ι) (θs : ℕ → Θ)
    (hθs : ∀ n, θs n ∈ H₀ i)
    (hi : Tendsto (fun n => P (θs n) (R i)) atTop (𝓝 α))
    (hj : ∀ j, j ≠ i → Tendsto (fun n => P (θs n) (R j)ᶜ) atTop (𝓝 0)) :
    ⨆ θ ∈ ⋃ i, H₀ i, P θ (⋂ j, R j) = α := by
  classical
  refine le_antisymm (iSup₂_le fun θ hθ => iut_level P H₀ R α hR hθ) ?_
  set S := ⨆ θ ∈ ⋃ i, H₀ i, P θ (⋂ j, R j) with hS
  have hg : Tendsto (fun n => S + ∑ j ∈ Finset.univ.erase i, P (θs n) (R j)ᶜ) atTop (𝓝 S) := by
    have := (tendsto_const_nhds (x := S) (f := atTop (α := ℕ))).add
      (tendsto_finsetSum (Finset.univ.erase i)
        fun j hj' => hj j (Finset.ne_of_mem_erase hj'))
    simpa using this
  refine le_of_tendsto_of_tendsto' hi hg fun n => ?_
  refine (measure_le_iInter_add_sum_compl (P (θs n)) R i).trans ?_
  gcongr
  exact le_iSup₂ (f := fun θ (_ : θ ∈ ⋃ i, H₀ i) => P θ (⋂ j, R j)) (θs n)
    (mem_iUnion.mpr ⟨i, hθs n⟩)

/-- `iut_size_eq` in Berger's form: for probability measures and measurable regions `R j`
(`j ≠ i`), the condition on the other regions is that their probability tends to one. -/
theorem iut_size_eq_of_measurable [Fintype ι] (P : Θ → Measure Ω)
    [∀ θ, IsProbabilityMeasure (P θ)] (H₀ : ι → Set Θ) (R : ι → Set Ω)
    (α : ℝ≥0∞) (hR : ∀ i, ∀ θ ∈ H₀ i, P θ (R i) ≤ α) (i : ι) (θs : ℕ → Θ)
    (hθs : ∀ n, θs n ∈ H₀ i)
    (hi : Tendsto (fun n => P (θs n) (R i)) atTop (𝓝 α))
    (hmeas : ∀ j, j ≠ i → MeasurableSet (R j))
    (hj : ∀ j, j ≠ i → Tendsto (fun n => P (θs n) (R j)) atTop (𝓝 1)) :
    ⨆ θ ∈ ⋃ i, H₀ i, P θ (⋂ j, R j) = α := by
  refine iut_size_eq P H₀ R α hR i θs hθs hi fun j hji => ?_
  have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞)) (f := atTop (α := ℕ)))
    (hj j hji) (Or.inl ENNReal.one_ne_top)
  simp only [tsub_self] at h
  refine h.congr fun n => ?_
  rw [prob_compl_eq_one_sub (hmeas j hji)]

/-- **Co-primary endpoints, power.** Under a probability measure, one is at most the
probability that all regions occur plus the sum of the probabilities that each one fails.
Any dependence, no measurability. -/
theorem one_le_measure_iInter_add_sum_compl [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R : ι → Set Ω) :
    1 ≤ μ (⋂ i, R i) + ∑ i, μ (R i)ᶜ := by
  have hsub : (univ : Set Ω) ⊆ (⋂ j, R j) ∪ ⋃ j ∈ (Finset.univ : Finset ι), (R j)ᶜ := by
    intro ω _
    by_cases h : ∀ j, ω ∈ R j
    · exact Or.inl (mem_iInter.mpr h)
    · push Not at h
      obtain ⟨j, hj⟩ := h
      exact Or.inr (mem_iUnion₂.mpr ⟨j, Finset.mem_univ _, hj⟩)
  calc (1 : ℝ≥0∞) = μ univ := measure_univ.symm
    _ ≤ μ ((⋂ j, R j) ∪ ⋃ j ∈ (Finset.univ : Finset ι), (R j)ᶜ) := measure_mono hsub
    _ ≤ μ (⋂ j, R j) + μ (⋃ j ∈ (Finset.univ : Finset ι), (R j)ᶜ) := measure_union_le _ _
    _ ≤ μ (⋂ j, R j) + ∑ j, μ (R j)ᶜ := by
        gcongr
        exact measure_biUnion_finset_le _ _

/-- **Co-primary endpoints, power bound.** If endpoint `i` fails to be significant with
probability at most `β i` (type II error, `β i ≥ 0`), then all endpoints are significant with
probability at least `1 - ∑ᵢ β i`, under any dependence. -/
theorem coprimary_power_ge [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ι → Set Ω) (β : ι → ℝ) (hβ0 : ∀ i, 0 ≤ β i)
    (hβ : ∀ i, μ (R i)ᶜ ≤ ENNReal.ofReal (β i)) :
    ENNReal.ofReal (1 - ∑ i, β i) ≤ μ (⋂ i, R i) := by
  rw [ENNReal.ofReal_sub _ (Finset.sum_nonneg fun i _ => hβ0 i), ENNReal.ofReal_one,
    ENNReal.ofReal_sum_of_nonneg fun i _ => hβ0 i, tsub_le_iff_right]
  exact (one_le_measure_iInter_add_sum_compl μ R).trans (by gcongr with i; exact hβ i)

/-- **Simultaneous claims from one lower confidence bound.** Let `τ` be the true parameter
value and `L` a lower bound with `μ (τ < L) ≤ α`. For any set `T` of thresholds, the
probability of making some false claim "`τ > t`" (claimed when `t < L`, false when `τ ≤ t`)
is at most `α`. -/
theorem measure_false_claim_le (μ : Measure Ω) (L : Ω → ℝ) (τ : ℝ) (α : ℝ≥0∞)
    (hL : μ {ω | τ < L ω} ≤ α) (T : Set ℝ) :
    μ {ω | ∃ t ∈ T, τ ≤ t ∧ t < L ω} ≤ α :=
  (measure_mono fun ω hω => by
    obtain ⟨t, _, h1, h2⟩ := hω
    exact (lt_of_le_of_lt h1 h2 : τ < L ω)).trans hL

/-- **Non-inferiority, then superiority** (Morikawa-Yoshida 1995, confidence-bound form).
With one lower confidence bound `L` of non-coverage at most `α`, claim non-inferiority when
`L > -δ` and superiority when `L > 0`. The probability of a false claim of either kind is at
most `α`. -/
theorem ni_then_superiority_fwer_le (μ : Measure Ω) (L : Ω → ℝ) (τ δ : ℝ) (α : ℝ≥0∞)
    (hL : μ {ω | τ < L ω} ≤ α) :
    μ {ω | (τ ≤ -δ ∧ -δ < L ω) ∨ (τ ≤ 0 ∧ 0 < L ω)} ≤ α := by
  refine (measure_mono fun ω hω => ?_).trans hL
  rcases hω with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact lt_of_le_of_lt h1 h2

open Applied.MultipleTesting in
open Classical in
/-- **Two nested tests at full level** (p-value form of non-inferiority then superiority).
If rejecting the second hypothesis always entails rejecting the first (`p 0 ≤ p 1`), then
testing both at level `α` is fixed-sequence testing, so the family-wise error rate is at most
`α` whichever of the two nulls are true. -/
theorem fwer_nested_two_le (P : Measure Ω) (p : Fin 2 → Ω → ℝ) (hnest : ∀ ω, p 0 ω ≤ p 1 ω)
    (H₀ : Finset (Fin 2)) (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) :
    fwer P H₀ (fun ω => {i | p i ω ≤ α}) ≤ ENNReal.ofReal α := by
  have h : (fun ω => ({i | p i ω ≤ α} : Finset (Fin 2))) = fixedSequence α p := by
    funext ω
    ext i
    simp only [fixedSequence, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hi j hj => ?_, fun hi => hi i le_rfl⟩
    fin_cases i <;> fin_cases j
    · exact hi
    · exact absurd hj (by decide)
    · exact (hnest ω).trans hi
    · exact hi
  rw [h]
  exact fwer_fixedSequence_le P p H₀ hp α hα

end General

/-! ### Normal laws through the standard normal cdf -/

local notation "Φ" => cdf (gaussianReal 0 1)

/-! The facts about `Φ` and about `N(θ, s²)` used below are proved once in
`Applied/Statistics/StandardNormal.lean` (namespace `Applied.StdNormal`). The names that this
file used to define are kept as aliases. -/

/-- The standard normal cdf is positive everywhere. Alias of `Applied.StdNormal.cdf_pos`. -/
alias cdf_stdNormal_pos := StdNormal.cdf_pos

/-- Symmetry of the standard normal cdf: `Φ (-x) = 1 - Φ x`. Alias of
`Applied.StdNormal.cdf_neg`. -/
alias cdf_stdNormal_neg := StdNormal.cdf_neg

/-- The standard normal cdf is below one everywhere. Alias of `Applied.StdNormal.cdf_lt_one`. -/
alias cdf_stdNormal_lt_one := StdNormal.cdf_lt_one

/-- `N(θ, s²)` is the law of `θ + s Z` for standard normal `Z`. Alias of
`Applied.StdNormal.gaussianReal_eq_map_stdNormal`. -/
alias gaussianReal_eq_map_stdNormal := StdNormal.gaussianReal_eq_map_stdNormal

/-- Lower tail of `N(θ, s²)`, `s ≠ 0`: `Φ((x - θ)/s)`. Alias of
`Applied.StdNormal.gaussianReal_Iic`. -/
alias gaussianReal_Iic := StdNormal.gaussianReal_Iic

/-- Upper tail of `N(θ, s²)`, `s ≠ 0`: `1 - Φ((x - θ)/s)`. Alias of
`Applied.StdNormal.gaussianReal_Ioi`. -/
alias gaussianReal_Ioi := StdNormal.gaussianReal_Ioi

/-- Open intervals under `N(θ, s²)`, `s ≠ 0`. For `b < a` both sides are zero. Alias of
`Applied.StdNormal.gaussianReal_Ioo`. -/
alias gaussianReal_Ioo := StdNormal.gaussianReal_Ioo

/-- Closed intervals under `N(θ, s²)`, `s ≠ 0`. Alias of `Applied.StdNormal.gaussianReal_Icc`. -/
alias gaussianReal_Icc := StdNormal.gaussianReal_Icc

/-- Moving the mean of a normal law away from a set lying below it decreases the set's
probability. Alias of `Applied.StdNormal.gaussianReal_anti_of_subset_Iic`. -/
alias gaussianReal_anti_of_subset_Iic := StdNormal.gaussianReal_anti_of_subset_Iic

variable {θ δ c : ℝ} {s : ℝ≥0}

/-! ### One-sided z-tests -/

/-- The upper one-sided z-test of `θ ≤ θ₀` (reject when `(x - θ₀)/s > c`) has level `1 - Φ c`. -/
theorem zTest_upper_level (hs : s ≠ 0) {θ₀ : ℝ} (hθ : θ ≤ θ₀) :
    gaussianReal θ (s ^ 2) {x | c < (x - θ₀) / s} ≤ ENNReal.ofReal (1 - Φ c) := by
  have hs' : (0 : ℝ) < s := by positivity
  have hset : {x : ℝ | c < (x - θ₀) / s} = Ioi (θ₀ + c * s) := by
    ext x
    simp only [mem_ofPred_eq, mem_Ioi, lt_div_iff₀ hs']
    constructor <;> intro h <;> linarith
  rw [hset, gaussianReal_Ioi _ _ hs]
  apply ENNReal.ofReal_le_ofReal
  have : c ≤ (θ₀ + c * s - θ) / s := by
    rw [le_div_iff₀ hs']
    linarith
  linarith [monotone_cdf (gaussianReal 0 1) this]

/-- The lower one-sided z-test of `θ ≥ θ₀` (reject when `(x - θ₀)/s < -c`) has level
`1 - Φ c`. -/
theorem zTest_lower_level (hs : s ≠ 0) {θ₀ : ℝ} (hθ : θ₀ ≤ θ) :
    gaussianReal θ (s ^ 2) {x | (x - θ₀) / s < -c} ≤ ENNReal.ofReal (1 - Φ c) := by
  have hs' : (0 : ℝ) < s := by positivity
  have hset : {x : ℝ | (x - θ₀) / s < -c} ⊆ Iic (θ₀ - c * s) := by
    intro x hx
    simp only [mem_ofPred_eq, div_lt_iff₀ hs'] at hx
    simp only [mem_Iic]
    linarith
  refine (measure_mono hset).trans ?_
  rw [gaussianReal_Iic _ _ hs]
  apply ENNReal.ofReal_le_ofReal
  have : (θ₀ - c * s - θ) / s ≤ -c := by
    rw [div_le_iff₀ hs']
    linarith
  have h := monotone_cdf (gaussianReal 0 1) this
  rw [cdf_stdNormal_neg] at h
  exact h

/-! ### Two one-sided tests (TOST) -/

/-- Rejection region of the two one-sided tests procedure for the null `|θ| ≥ δ`, with
standard error `s` and critical value `c`: the z-test of `θ ≤ -δ` and the z-test of `θ ≥ δ`
both reject. -/
def tostRegion (δ s c : ℝ) : Set ℝ := {x | c < (x - -δ) / s ∧ (x - δ) / s < -c}

/-- For standard error `s > 0` the TOST rejection region is the open interval
`(-δ + c s, δ - c s)` of estimates (empty when `c s ≥ δ`). -/
lemma tostRegion_eq_Ioo {δ s c : ℝ} (hs : 0 < s) :
    tostRegion δ s c = Ioo (-δ + c * s) (δ - c * s) := by
  ext x
  simp only [tostRegion, mem_ofPred_eq, mem_Ioo, lt_div_iff₀ hs, div_lt_iff₀ hs]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **TOST as interval inclusion** (Schuirmann 1987). For `s > 0` and `c ≥ 0`, both one-sided
tests reject iff the interval `[x - c s, x + c s]` lies inside `(-δ, δ)`. -/
theorem mem_tostRegion_iff_ci {δ s c x : ℝ} (hs : 0 < s) (hc : 0 ≤ c) :
    x ∈ tostRegion δ s c ↔ Icc (x - c * s) (x + c * s) ⊆ Ioo (-δ) δ := by
  have hcs : 0 ≤ c * s := mul_nonneg hc hs.le
  rw [tostRegion_eq_Ioo hs, Icc_subset_Ioo_iff (by linarith), mem_Ioo]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The interval `[x - c s, x + c s]` covers the mean with probability `1 - 2 (1 - Φ c)`
(the right side is read as zero when it is negative, which happens only for `c < 0`). -/
theorem ci_coverage (hs : s ≠ 0) (θ c : ℝ) :
    gaussianReal θ (s ^ 2) {x | θ ∈ Icc (x - c * s) (x + c * s)}
      = ENNReal.ofReal (1 - 2 * (1 - Φ c)) := by
  have hs' : (0 : ℝ) < s := by positivity
  have hset : {x : ℝ | θ ∈ Icc (x - c * s) (x + c * s)} = Icc (θ - c * s) (θ + c * s) := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset, gaussianReal_Icc _ _ _ hs]
  congr 1
  have e1 : (θ + c * s - θ) / s = c := by field_simp; ring
  have e2 : (θ - c * s - θ) / s = -c := by field_simp; ring
  rw [e1, e2, cdf_stdNormal_neg]
  ring

/-- **Rejection probability of TOST** under `N(θ, s²)`, `s ≠ 0`:
`Φ((δ - θ)/s - c) - Φ(c - (δ + θ)/s)`, read as zero when negative. -/
theorem tost_prob (hs : s ≠ 0) (θ δ c : ℝ) :
    gaussianReal θ (s ^ 2) (tostRegion δ s c)
      = ENNReal.ofReal (Φ ((δ - θ) / s - c) - Φ (c - (δ + θ) / s)) := by
  have hs' : (0 : ℝ) < s := by positivity
  rw [tostRegion_eq_Ioo hs', gaussianReal_Ioo _ _ _ hs]
  have e1 : (δ - c * s - θ) / s = (δ - θ) / s - c := by field_simp; ring
  have e2 : (-δ + c * s - θ) / s = c - (δ + θ) / s := by field_simp; ring
  rw [e1, e2]

/-- The TOST rejection probability is the same at `θ` and `-θ`. -/
theorem tost_prob_neg (hs : s ≠ 0) (θ δ c : ℝ) :
    gaussianReal (-θ) (s ^ 2) (tostRegion δ s c) = gaussianReal θ (s ^ 2) (tostRegion δ s c) := by
  rw [tost_prob hs, tost_prob hs]
  congr 1
  have h1 := cdf_stdNormal_neg (c - (δ - θ) / s)
  have h2 := cdf_stdNormal_neg (c - (δ + θ) / s)
  rw [neg_sub] at h1 h2
  have e1 : (δ - -θ) / (s : ℝ) = (δ + θ) / s := by ring
  have e2 : (δ + -θ) / (s : ℝ) = (δ - θ) / s := by ring
  rw [e1, e2]
  linarith

/-- **TOST at the margin** `θ = δ`: the rejection probability is
`(1 - Φ c) - Φ (c - 2 δ / s)`, read as zero when negative. -/
theorem tost_prob_at_margin (hs : s ≠ 0) (δ c : ℝ) :
    gaussianReal δ (s ^ 2) (tostRegion δ s c)
      = ENNReal.ofReal ((1 - Φ c) - Φ (c - 2 * δ / s)) := by
  rw [tost_prob hs]
  congr 1
  have e1 : (δ - δ) / (s : ℝ) - c = -c := by simp
  have e2 : c - (δ + δ) / (s : ℝ) = c - 2 * δ / s := by ring
  rw [e1, e2, cdf_stdNormal_neg]

/-- **TOST at the margin** `θ = -δ`: same value as at `θ = δ`. -/
theorem tost_prob_at_neg_margin (hs : s ≠ 0) (δ c : ℝ) :
    gaussianReal (-δ) (s ^ 2) (tostRegion δ s c)
      = ENNReal.ofReal ((1 - Φ c) - Φ (c - 2 * δ / s)) := by
  rw [tost_prob_neg hs, tost_prob_at_margin hs]

/-- **TOST has level `1 - Φ c`** on the null `|θ| ≥ δ`: this is the intersection-union
argument applied to the two one-sided z-tests. No sign condition on `c` or `δ`. -/
theorem tost_level (hs : s ≠ 0) (hθ : δ ≤ |θ|) :
    gaussianReal θ (s ^ 2) (tostRegion δ s c) ≤ ENNReal.ofReal (1 - Φ c) := by
  rcases le_abs.mp hθ with h | h
  · have hsub : tostRegion δ s c ⊆ {x | (x - δ) / s < -c} := fun x hx => hx.2
    exact (measure_mono hsub).trans (zTest_lower_level hs h)
  · have hsub : tostRegion δ s c ⊆ {x | c < (x - -δ) / s} := fun x hx => hx.1
    exact (measure_mono hsub).trans (zTest_upper_level hs (by linarith))

/-- For `c ≥ 0` the TOST rejection probability on the null `|θ| ≥ δ` is largest at the
margin. The hypothesis `c ≥ 0` is a convenience of the proof (the rejection interval then lies
to the left of `δ`); for `δ ≥ 0` the statement is true for every real `c`, because the
interval is symmetric about `0`, but that version is not proved here. -/
theorem tost_prob_le_margin (hs : s ≠ 0) (hc : 0 ≤ c) (hθ : δ ≤ |θ|) :
    gaussianReal θ (s ^ 2) (tostRegion δ s c)
      ≤ ENNReal.ofReal ((1 - Φ c) - Φ (c - 2 * δ / s)) := by
  have hs' : (0 : ℝ) < s := by positivity
  have key : ∀ θ' : ℝ, δ ≤ θ' →
      gaussianReal θ' (s ^ 2) (tostRegion δ s c) ≤ gaussianReal δ (s ^ 2) (tostRegion δ s c) := by
    intro θ' h
    refine gaussianReal_anti_of_subset_Iic h (pow_ne_zero 2 hs) ?_ ?_
    · rw [tostRegion_eq_Ioo hs']
      exact measurableSet_Ioo
    · rw [tostRegion_eq_Ioo hs']
      intro x hx
      have := mul_nonneg hc hs'.le
      exact (hx.2.le.trans (by linarith) : x ≤ δ)
  rw [← tost_prob_at_margin hs]
  rcases le_abs.mp hθ with h | h
  · exact key θ h
  · rw [← tost_prob_neg hs]
    exact key (-θ) h

/-- **Size of TOST.** For `s ≠ 0` and `c ≥ 0`, the supremum of the rejection probability over
the null `|θ| ≥ δ` equals `(1 - Φ c) - Φ (c - 2 δ / s)` (zero when this is negative). As in
`tost_prob_le_margin`, `c ≥ 0` is assumed for convenience and could be replaced by `δ ≥ 0`. -/
theorem tost_size (hs : s ≠ 0) (hc : 0 ≤ c) (δ : ℝ) :
    ⨆ θ : ℝ, ⨆ _ : δ ≤ |θ|, gaussianReal θ (s ^ 2) (tostRegion δ s c)
      = ENNReal.ofReal ((1 - Φ c) - Φ (c - 2 * δ / s)) := by
  refine le_antisymm (iSup₂_le fun θ hθ => tost_prob_le_margin hs hc hθ) ?_
  exact le_iSup₂_of_le δ (le_abs_self δ) (tost_prob_at_margin hs δ c).ge

/-- **TOST is conservative**: its size is strictly below the nominal level `1 - Φ c`. -/
theorem tost_size_lt (hs : s ≠ 0) (hc : 0 ≤ c) (δ : ℝ) :
    ⨆ θ : ℝ, ⨆ _ : δ ≤ |θ|, gaussianReal θ (s ^ 2) (tostRegion δ s c)
      < ENNReal.ofReal (1 - Φ c) := by
  rw [tost_size hs hc]
  have h1 := cdf_stdNormal_lt_one c
  have h2 := cdf_stdNormal_pos (c - 2 * δ / s)
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)

/-- `tost_prob` for an estimator `X` on any measure space whose law is `N(θ, s²)`. -/
theorem tost_prob_of_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X P) (hs : s ≠ 0) (hlaw : P.map X = gaussianReal θ (s ^ 2)) (δ c : ℝ) :
    P {ω | X ω ∈ tostRegion δ s c}
      = ENNReal.ofReal (Φ ((δ - θ) / s - c) - Φ (c - (δ + θ) / s)) := by
  have hs' : (0 : ℝ) < s := by positivity
  have hmeas : MeasurableSet (tostRegion δ s c) := by
    rw [tostRegion_eq_Ioo hs']
    exact measurableSet_Ioo
  rw [← tost_prob hs, ← hlaw, Measure.map_apply_of_aemeasurable hX hmeas]
  rfl

/-- `tost_level` for an estimator `X` on any measure space whose law is `N(θ, s²)`. -/
theorem tost_level_of_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X P) (hs : s ≠ 0) (hlaw : P.map X = gaussianReal θ (s ^ 2))
    (hθ : δ ≤ |θ|) :
    P {ω | X ω ∈ tostRegion δ s c} ≤ ENNReal.ofReal (1 - Φ c) := by
  have hs' : (0 : ℝ) < s := by positivity
  have hmeas : MeasurableSet (tostRegion δ s c) := by
    rw [tostRegion_eq_Ioo hs']
    exact measurableSet_Ioo
  have := tost_level (c := c) hs hθ
  rwa [← hlaw, Measure.map_apply_of_aemeasurable hX hmeas] at this

/-! ### Non-inferiority, then superiority, for a normal mean -/

/-- The lower confidence bound `x - c s` exceeds the mean with probability `1 - Φ c`. -/
theorem lower_bound_noncoverage (hs : s ≠ 0) (θ c : ℝ) :
    gaussianReal θ (s ^ 2) {x | θ < x - c * s} = ENNReal.ofReal (1 - Φ c) := by
  have hs' : (0 : ℝ) < s := by positivity
  have hset : {x : ℝ | θ < x - c * s} = Ioi (θ + c * s) := by
    ext x
    simp only [mem_ofPred_eq, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [hset, gaussianReal_Ioi _ _ hs]
  have e1 : (θ + c * s - θ) / s = c := by field_simp; ring
  rw [e1]

/-- **Non-inferiority, then superiority, for a normal mean with known standard error.** Claim
non-inferiority (`θ > -δ`) when `x - c s > -δ` and superiority (`θ > 0`) when `x - c s > 0`.
Under every `θ`, the probability of a false claim of either kind is at most `1 - Φ c`. -/
theorem ni_then_superiority_gaussian (hs : s ≠ 0) (θ δ c : ℝ) :
    gaussianReal θ (s ^ 2) {x | (θ ≤ -δ ∧ -δ < x - c * s) ∨ (θ ≤ 0 ∧ 0 < x - c * s)}
      ≤ ENNReal.ofReal (1 - Φ c) :=
  ni_then_superiority_fwer_le _ (fun x => x - c * s) θ δ _ (lower_bound_noncoverage hs θ c).le

end Applied.IntersectionUnion
