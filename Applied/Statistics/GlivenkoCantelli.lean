import Mathlib.Probability.StrongLaw
import Mathlib.Probability.CDF

/-!
# Glivenko–Cantelli theorem

For real random variables `X 0, X 1, …` the empirical frequency of a set `s` after `n`
observations is `#{i < n | X i ∈ s} / n`, and the empirical cdf at `t` is the empirical
frequency of `(-∞, t]`.

* `tendsto_empiricalFreq`: for pairwise independent, identically distributed observations the
  empirical frequency of a measurable set converges almost surely to its probability (the
  strong law of large numbers applied to indicators).
* `tendsto_empiricalCDF`: pointwise almost-sure convergence of the empirical cdf.
* `glivenkoCantelli_eventually`, `glivenkoCantelli`: the **Glivenko–Cantelli theorem**: almost
  surely, the empirical cdf converges to the cdf of `X 0` uniformly on `ℝ`.

The proof of the uniform statement uses the quantiles `u_q = inf {s | q ≤ F s}` for
`q = j / K`: the empirical cdf and its left limits converge at these countably many points,
and monotonicity controls every other point up to `1 / K`.
-/

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped Topology Function

namespace Applied.Statistics

section Quantile

variable (μ : Measure ℝ)

/-- The lower `q`-quantile of a probability measure on `ℝ`: `inf {s | q ≤ F s}`. -/
noncomputable def lowerQuantile (q : ℝ) : ℝ := sInf {s | q ≤ cdf μ s}

variable {μ} {q : ℝ}

private theorem quantileSet_nonempty (hq1 : q < 1) : {s | q ≤ cdf μ s}.Nonempty :=
  ((tendsto_cdf_atTop μ).eventually_const_le hq1).exists

private theorem quantileSet_bddBelow (hq0 : 0 < q) : BddBelow {s | q ≤ cdf μ s} := by
  obtain ⟨s₀, hs₀⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const hq0).exists
  refine ⟨s₀, fun s (hs : q ≤ cdf μ s) => ?_⟩
  by_contra hlt
  exact absurd (hs.trans (monotone_cdf μ (not_le.mp hlt).le)) (not_le.mpr hs₀)

theorem lowerQuantile_le (hq0 : 0 < q) {t : ℝ} (ht : q ≤ cdf μ t) : lowerQuantile μ q ≤ t :=
  csInf_le (quantileSet_bddBelow hq0) ht

theorem cdf_lt_of_lt_lowerQuantile (hq0 : 0 < q) {t : ℝ} (ht : t < lowerQuantile μ q) :
    cdf μ t < q := by
  by_contra h
  exact absurd (lowerQuantile_le hq0 (not_lt.mp h)) (not_le.mpr ht)

/-- The cdf at the `q`-quantile is at least `q` (by right-continuity). -/
theorem le_cdf_lowerQuantile (hq0 : 0 < q) (hq1 : q < 1) : q ≤ cdf μ (lowerQuantile μ q) := by
  by_contra h
  have hev : ∀ᶠ x in 𝓝[≥] lowerQuantile μ q, cdf μ x < q :=
    ((cdf μ).right_continuous (lowerQuantile μ q)).eventually_lt_const (not_le.mp h)
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
  obtain ⟨s, hs, hsb⟩ := exists_lt_of_csInf_lt (quantileSet_nonempty hq1) (mem_Ioi.mp hb)
  have hs' : q ≤ cdf μ s := hs
  have : cdf μ s < q := hsub ⟨lowerQuantile_le hq0 hs', hsb⟩
  exact absurd hs' (not_le.mpr this)

theorem lt_lowerQuantile_of_cdf_lt (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ} (ht : cdf μ t < q) :
    t < lowerQuantile μ q := by
  by_contra h
  exact absurd ((le_cdf_lowerQuantile hq0 hq1).trans (monotone_cdf μ (not_lt.mp h)))
    (not_le.mpr ht)

/-- The probability of lying strictly below the `q`-quantile is at most `q`. -/
theorem measureReal_Iio_lowerQuantile_le [IsProbabilityMeasure μ] (hq0 : 0 < q) :
    μ.real (Iio (lowerQuantile μ q)) ≤ q := by
  have hlim : Function.leftLim (cdf μ) (lowerQuantile μ q) ≤ q := by
    refine le_of_tendsto ((monotone_cdf μ).tendsto_leftLim _) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (cdf_lt_of_lt_lowerQuantile hq0 (mem_Iio.mp hs)).le
  have h := (cdf μ).measure_Iio (tendsto_cdf_atBot μ) (lowerQuantile μ q)
  rw [measure_cdf, sub_zero] at h
  rw [measureReal_def, h]
  exact ENNReal.toReal_le_of_le_ofReal hq0.le (ENNReal.ofReal_le_ofReal hlim)

end Quantile

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The empirical frequency of the set `s` among the first `n` observations. -/
noncomputable def empiricalFreq (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (s : Set ℝ) : ℝ :=
  (∑ i ∈ range n, s.indicator (fun _ => (1 : ℝ)) (X i ω)) / n

/-- The empirical cumulative distribution function of the first `n` observations. -/
noncomputable def empiricalCDF (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  empiricalFreq X n ω (Iic t)

theorem empiricalFreq_nonneg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (s : Set ℝ) :
    0 ≤ empiricalFreq X n ω s :=
  div_nonneg (sum_nonneg fun _ _ => indicator_nonneg (fun _ _ => zero_le_one) _)
    (Nat.cast_nonneg n)

theorem empiricalFreq_le_one (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (s : Set ℝ) :
    empiricalFreq X n ω s ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg n)
  calc ∑ i ∈ range n, s.indicator (fun _ => (1 : ℝ)) (X i ω) ≤ ∑ _i ∈ range n, (1 : ℝ) :=
        sum_le_sum fun i _ => indicator_le_self' (fun _ _ => zero_le_one) _
    _ = n := by simp

theorem empiricalFreq_mono (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {s s' : Set ℝ} (h : s ⊆ s') :
    empiricalFreq X n ω s ≤ empiricalFreq X n ω s' := by
  unfold empiricalFreq
  gcongr

/-- **Strong law for empirical frequencies**: for pairwise independent identically distributed
observations, the empirical frequency of a measurable set converges almost surely to its
probability under the law of `X 0`. -/
theorem tendsto_empiricalFreq [IsProbabilityMeasure P] (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {s : Set ℝ} (hs : MeasurableSet s) :
    ∀ᵐ ω ∂P, Tendsto (fun n => empiricalFreq X n ω s) atTop (𝓝 ((P.map (X 0)).real s)) := by
  set g : ℝ → ℝ := s.indicator (fun _ => (1 : ℝ)) with hg
  have hgm : Measurable g := measurable_const.indicator hs
  have hX0 : AEMeasurable (X 0) P := (hident 0).aemeasurable_fst
  have hint : Integrable (g ∘ X 0) P := by
    refine (integrable_const (1 : ℝ)).mono' (hgm.comp_aemeasurable hX0).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    simp only [Function.comp_apply, hg, indicator]
    split_ifs <;> simp
  have hmean : ∫ ω, (g ∘ X 0) ω ∂P = (P.map (X 0)).real s := by
    have h1 : ∫ ω, (g ∘ X 0) ω ∂P = ∫ y, g y ∂(P.map (X 0)) :=
      (integral_map hX0 hgm.aestronglyMeasurable).symm
    rw [h1, hg, integral_indicator_const _ hs]
    exact mul_one _
  have h := strong_law_ae_real (fun i => g ∘ X i) hint
    (fun i j hij => (hindep hij).comp hgm hgm) (fun i => (hident i).comp hgm)
  rw [hmean] at h
  exact h

/-- Pointwise almost-sure convergence of the empirical cdf to the cdf of `X 0`. -/
theorem tendsto_empiricalCDF [IsProbabilityMeasure P] (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (t : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => empiricalCDF X n ω t) atTop (𝓝 (cdf (P.map (X 0)) t)) := by
  rw [cdf_eq_real]
  exact tendsto_empiricalFreq hindep hident measurableSet_Iic

/-- Deterministic core of the Glivenko–Cantelli theorem: if the empirical frequencies of
`(-∞, u]` and `(-∞, u)` are within `δ` of their probabilities at the quantiles
`u = u_{j/(k+1)}`, `j ≤ k`, then the empirical cdf is uniformly within `1/(k+1) + δ` of the
cdf. -/
theorem abs_empiricalCDF_sub_cdf_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hIic : ∀ j ∈ range (k + 1), |empiricalFreq X n ω (Iic (lowerQuantile μ (j / (k + 1 : ℝ))))
      - μ.real (Iic (lowerQuantile μ (j / (k + 1 : ℝ))))| ≤ δ)
    (hIio : ∀ j ∈ range (k + 1), |empiricalFreq X n ω (Iio (lowerQuantile μ (j / (k + 1 : ℝ))))
      - μ.real (Iio (lowerQuantile μ (j / (k + 1 : ℝ))))| ≤ δ) (t : ℝ) :
    |empiricalCDF X n ω t - cdf μ t| ≤ 1 / (k + 1 : ℝ) + δ := by
  have hK : (0 : ℝ) < k + 1 := by positivity
  have hF0 : 0 ≤ cdf μ t := cdf_nonneg μ t
  have hF1 : cdf μ t ≤ 1 := cdf_le_one μ t
  have hE0 := empiricalFreq_nonneg X n ω (Iic t)
  have hE1 := empiricalFreq_le_one X n ω (Iic t)
  have hinv : 0 ≤ 1 / (k + 1 : ℝ) := by positivity
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- lower bound, using the quantile just below `F t`
    set j := min ⌊(k + 1 : ℝ) * cdf μ t⌋₊ k with hj
    have hjk : j ≤ k := min_le_right _ _
    have hjle : (j : ℝ) / (k + 1) ≤ cdf μ t := by
      rw [div_le_iff₀ hK, mul_comm]
      exact (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le (by positivity))
    have hjge : cdf μ t ≤ ((j : ℝ) + 1) / (k + 1) := by
      rw [le_div_iff₀ hK, mul_comm]
      rcases min_choice ⌊(k + 1 : ℝ) * cdf μ t⌋₊ k with h | h
      · rw [hj, h]; exact (Nat.lt_floor_add_one _).le
      · rw [hj, h]; nlinarith
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0] at hjge
      simp only [Nat.cast_zero, zero_add] at hjge
      unfold empiricalCDF
      linarith
    · have hq0 : (0 : ℝ) < j / (k + 1) := by positivity
      have hq1 : (j : ℝ) / (k + 1) < 1 := by
        rw [div_lt_one hK]
        exact_mod_cast Nat.lt_succ_of_le hjk
      have hmono : empiricalFreq X n ω (Iic (lowerQuantile μ (j / (k + 1 : ℝ))))
          ≤ empiricalFreq X n ω (Iic t) :=
        empiricalFreq_mono X n ω (Iic_subset_Iic.mpr (lowerQuantile_le hq0 hjle))
      have hconv := (abs_le.mp (hIic j (mem_range.mpr (Nat.lt_succ_of_le hjk)))).1
      have hq := le_cdf_lowerQuantile (μ := μ) hq0 hq1
      rw [cdf_eq_real] at hq
      have : ((j : ℝ) + 1) / (k + 1) = j / (k + 1) + 1 / (k + 1) := by ring
      unfold empiricalCDF
      linarith
  · -- upper bound, using the quantile just above `F t`
    set j := ⌊(k + 1 : ℝ) * cdf μ t⌋₊ + 1 with hj
    have hjgt : cdf μ t < (j : ℝ) / (k + 1) := by
      rw [lt_div_iff₀ hK, mul_comm, hj]
      exact_mod_cast Nat.lt_floor_add_one _
    have hjle : (j : ℝ) / (k + 1) ≤ cdf μ t + 1 / (k + 1) := by
      have h1 : (j : ℝ) ≤ (k + 1) * cdf μ t + 1 := by
        rw [hj]; push_cast
        linarith [Nat.floor_le (show (0 : ℝ) ≤ (k + 1) * cdf μ t by positivity)]
      have : cdf μ t + 1 / (k + 1 : ℝ) = ((k + 1) * cdf μ t + 1) / (k + 1) := by
        field_simp
      rw [this]
      gcongr
    rcases Nat.lt_or_ge k j with hkj | hjk
    · have : (1 : ℝ) ≤ j / (k + 1) := by
        rw [one_le_div hK]
        exact_mod_cast hkj
      unfold empiricalCDF
      linarith
    · have hq0 : (0 : ℝ) < j / (k + 1) := by rw [hj]; positivity
      have hq1 : (j : ℝ) / (k + 1) < 1 := by
        rw [div_lt_one hK]
        exact_mod_cast Nat.lt_succ_of_le hjk
      have hmono : empiricalFreq X n ω (Iic t)
          ≤ empiricalFreq X n ω (Iio (lowerQuantile μ (j / (k + 1 : ℝ)))) :=
        empiricalFreq_mono X n ω
          (Iic_subset_Iio.mpr (lt_lowerQuantile_of_cdf_lt hq0 hq1 hjgt))
      have hconv := (abs_le.mp (hIio j (mem_range.mpr (Nat.lt_succ_of_le hjk)))).2
      have hq := measureReal_Iio_lowerQuantile_le (μ := μ) hq0
      unfold empiricalCDF
      linarith

/-- **Glivenko–Cantelli theorem**, `ε`–`N` form: almost surely, for every `ε > 0` the empirical
cdf is eventually within `ε` of the cdf of `X 0`, simultaneously at all points. -/
theorem glivenkoCantelli_eventually [IsProbabilityMeasure P]
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop, ∀ t, |empiricalCDF X n ω t - cdf (P.map (X 0)) t| ≤ ε := by
  set μ := P.map (X 0) with hμ
  have h1 : ∀ᵐ ω ∂P, ∀ k j : ℕ, Tendsto
      (fun n => empiricalFreq X n ω (Iic (lowerQuantile μ (j / (k + 1 : ℝ))))) atTop
      (𝓝 (μ.real (Iic (lowerQuantile μ (j / (k + 1 : ℝ)))))) :=
    ae_all_iff.mpr fun k => ae_all_iff.mpr fun j =>
      tendsto_empiricalFreq hindep hident measurableSet_Iic
  have h2 : ∀ᵐ ω ∂P, ∀ k j : ℕ, Tendsto
      (fun n => empiricalFreq X n ω (Iio (lowerQuantile μ (j / (k + 1 : ℝ))))) atTop
      (𝓝 (μ.real (Iio (lowerQuantile μ (j / (k + 1 : ℝ)))))) :=
    ae_all_iff.mpr fun k => ae_all_iff.mpr fun j =>
      tendsto_empiricalFreq hindep hident measurableSet_Iio
  filter_upwards [h1, h2] with ω hω1 hω2 ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  have hδ : (0 : ℝ) < ε / 2 := half_pos hε
  have e1 : ∀ᶠ n in atTop, ∀ j ∈ range (k + 1),
      |empiricalFreq X n ω (Iic (lowerQuantile μ (j / (k + 1 : ℝ))))
        - μ.real (Iic (lowerQuantile μ (j / (k + 1 : ℝ))))| ≤ ε / 2 :=
    (eventually_all_finset _).mpr fun j _ => by
      have := (hω1 k j).eventually (Metric.closedBall_mem_nhds _ hδ)
      simpa [Real.dist_eq] using this
  have e2 : ∀ᶠ n in atTop, ∀ j ∈ range (k + 1),
      |empiricalFreq X n ω (Iio (lowerQuantile μ (j / (k + 1 : ℝ))))
        - μ.real (Iio (lowerQuantile μ (j / (k + 1 : ℝ))))| ≤ ε / 2 :=
    (eventually_all_finset _).mpr fun j _ => by
      have := (hω2 k j).eventually (Metric.closedBall_mem_nhds _ hδ)
      simpa [Real.dist_eq] using this
  filter_upwards [e1, e2] with n hn1 hn2 t
  have := abs_empiricalCDF_sub_cdf_le (μ := μ) X n ω k hδ.le hn1 hn2 t
  linarith

/-- **Glivenko–Cantelli theorem**: for pairwise independent, identically distributed real
observations, the empirical cdf converges almost surely to the cdf of `X 0`, uniformly on `ℝ`:
`sup_t |F_n(t) - F(t)| → 0`. -/
theorem glivenkoCantelli [IsProbabilityMeasure P]
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ⨆ t, |empiricalCDF X n ω t - cdf (P.map (X 0)) t|)
      atTop (𝓝 0) := by
  filter_upwards [glivenkoCantelli_eventually hindep hident] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω (ε / 2) (half_pos hε))
  refine ⟨N, fun n hn => ?_⟩
  have h0 : 0 ≤ ⨆ t, |empiricalCDF X n ω t - cdf (P.map (X 0)) t| :=
    Real.iSup_nonneg fun t => abs_nonneg _
  have h1 : ⨆ t, |empiricalCDF X n ω t - cdf (P.map (X 0)) t| ≤ ε / 2 := ciSup_le (hN n hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

end Applied.Statistics
