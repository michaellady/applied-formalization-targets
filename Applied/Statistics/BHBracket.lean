import Applied.Statistics.BHMonotone

/-!
# Bracketing the Benjamini–Hochberg threshold by counts at finitely many thresholds

Finite-sample, deterministic versions of Lemmas 2 and 3 of E. Dobriban, "The
Benjamini–Hochberg Procedure Can Fail to Control the FDR for Correlated Two-Sided Gaussian
Tests" (arXiv:2607.12208, 2026), which are stated there for limits of empirical distribution
functions. Here `q : ι → ℝ` is any vector of `m = |ι|` p-values and the Benjamini–Hochberg
p-value threshold is `α * bhK α q / m`.

* `cntLE S q t`: the number of indices `i ∈ S` with `q i ≤ t`.
* `bhThreshold_le_of_cells`: if `(w, α]` is covered by cells `(lo j, hi j]` and in each cell
  fewer than `m * lo j / α` p-values are at most `hi j`, the threshold is at most `w`.
* `le_bhThreshold_of_count`: if `v ≤ α` and at least `m v / α + 1` p-values are at most `v`,
  the threshold is at least `v`.
* `fdp_bhReject_ge_of_bracket`: with both, and at least `m f` true-null p-values at most `v`,
  the false discovery proportion is at least `α f / w`.
-/

open Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {ι : Type*} [Fintype ι] {α : ℝ}

/-- Number of indices in `S` whose p-value is at most `t`. -/
noncomputable def cntLE (S : Finset ι) (q : ι → ℝ) (t : ℝ) : ℕ := (S.filter fun i => q i ≤ t).card

omit [Fintype ι] in
lemma cntLE_mono (S : Finset ι) (q : ι → ℝ) {s t : ℝ} (h : s ≤ t) : cntLE S q s ≤ cntLE S q t :=
  Finset.card_le_card fun i hi => by
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans h⟩

lemma bhCount_eq_cntLE (q : ι → ℝ) (k : ℕ) :
    bhCount α q k = cntLE univ q (α * k / Fintype.card ι) := rfl

/-- **Upper bracket.** Suppose every `t ∈ (w, α]` lies in some cell `(lo j, hi j]` in which
fewer than `m * lo j / α` p-values are at most `hi j`. Then the Benjamini–Hochberg p-value
threshold `α K / m` is at most `w`. -/
theorem bhThreshold_le_of_cells (hα : 0 < α) (q : ι → ℝ) {w : ℝ} (hw : 0 ≤ w) {J : Type*}
    (lo hi : J → ℝ)
    (hcover : ∀ t, w < t → t ≤ α → ∃ j, lo j < t ∧ t ≤ hi j)
    (hcell : ∀ j, (cntLE univ q (hi j) : ℝ) < Fintype.card ι * lo j / α) :
    α * bhK α q / Fintype.card ι ≤ w := by
  by_contra hlt
  rw [not_le] at hlt
  set K := bhK α q with hK
  set m := Fintype.card ι with hm
  have hKm : K ≤ m := bhK_le q
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0] at hlt; simp at hlt; linarith
    · exact h0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hK0.trans_le hKm
  have hle : α * K / m ≤ α := by
    rw [div_le_iff₀ hmpos]
    have : (K : ℝ) ≤ m := by exact_mod_cast hKm
    nlinarith
  obtain ⟨j, hj1, hj2⟩ := hcover _ hlt hle
  have h1 : (K : ℝ) ≤ cntLE univ q (hi j) := by
    have := (bhK_le_bhCount (α := α) q).trans (cntLE_mono univ q hj2)
    exact_mod_cast this
  have h2 : (m : ℝ) * lo j / α < K := by
    rw [div_lt_iff₀ hα]
    have := (lt_div_iff₀ hmpos).mp hj1
    linarith
  linarith [hcell j]

/-- **Lower bracket.** If `v ≤ α` and at least `m v / α + 1` p-values are at most `v`, then the
Benjamini–Hochberg p-value threshold `α K / m` is at least `v`. -/
theorem le_bhThreshold_of_count (hα : 0 < α) (q : ι → ℝ) {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ α)
    (hcount : (Fintype.card ι : ℝ) * v / α + 1 ≤ cntLE univ q v) :
    v ≤ α * bhK α q / Fintype.card ι := by
  set m := Fintype.card ι with hm
  have hmpos : (0 : ℝ) < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have hc : cntLE univ q v ≤ m := Finset.card_le_univ _
      have hc' : (cntLE univ q v : ℝ) ≤ 0 := by
        have : (cntLE univ q v : ℝ) ≤ m := by exact_mod_cast hc
        simpa [h0] using this
      have : (0 : ℝ) ≤ (m : ℝ) * v / α := by positivity
      linarith
    · exact_mod_cast h0
  set x := (m : ℝ) * v / α with hx
  have hx0 : 0 ≤ x := by positivity
  have hxm : x ≤ m := by
    rw [hx, div_le_iff₀ hα]
    nlinarith
  set K₁ := ⌈x⌉₊ with hK₁
  have hK₁m : K₁ ≤ m := Nat.ceil_le.mpr hxm
  have hxK : x ≤ K₁ := Nat.le_ceil x
  have hKlt : (K₁ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hvK : v ≤ α * K₁ / m := by
    rw [le_div_iff₀ hmpos]
    have := (div_le_iff₀ hα).mp hxK
    linarith
  have hfeas : K₁ ≤ bhCount α q K₁ := by
    have h1 : cntLE univ q v ≤ bhCount α q K₁ := cntLE_mono univ q hvK
    have h2 : (K₁ : ℝ) < cntLE univ q v := hKlt.trans_le hcount
    have h3 : K₁ < cntLE univ q v := by exact_mod_cast h2
    omega
  have hKK : (K₁ : ℝ) ≤ bhK α q := by exact_mod_cast le_bhK q hK₁m hfeas
  refine hvK.trans ?_
  gcongr

variable [DecidableEq ι]

/-- **Bracketing gives a lower bound on the false discovery proportion.** If the
Benjamini–Hochberg p-value threshold lies in `[v, w]` with `0 < v`, `0 < w`, and at least `m f`
true-null p-values are at most `v`, then the false discovery proportion is at least
`α f / w`. -/
theorem fdp_bhReject_ge_of_threshold (hα : 0 < α) (q : ι → ℝ) (H₀ : Finset ι) {v w f : ℝ}
    (hv0 : 0 < v) (hw0 : 0 < w) (hf : 0 ≤ f)
    (hlow : v ≤ α * bhK α q / Fintype.card ι) (hupp : α * bhK α q / Fintype.card ι ≤ w)
    (hnull : (Fintype.card ι : ℝ) * f ≤ cntLE H₀ q v) :
    ENNReal.ofReal (α * f / w) ≤ fdp H₀ (bhReject α q) := by
  set m := Fintype.card ι with hm
  set K := bhK α q with hK
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0] at hlow; simp at hlow; linarith
    · exact h0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hK0.trans_le (bhK_le q)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hV : cntLE H₀ q v ≤ (bhReject α q ∩ H₀).card := by
    refine Finset.card_le_card fun i hi => ?_
    rw [mem_filter] at hi
    exact Finset.mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hi.2.trans hlow⟩, hi.1⟩
  have hR : (bhReject α q).card = K := card_bhReject hα.le q
  rw [fdp, hR]
  have hVr : (m : ℝ) * f ≤ ((bhReject α q ∩ H₀).card : ℝ) :=
    hnull.trans (by exact_mod_cast hV)
  have hKw : (K : ℝ) * α ≤ w * m := by
    have := (div_le_iff₀ hmpos).mp hupp
    linarith
  have hreal : α * f / w ≤ ((bhReject α q ∩ H₀).card : ℝ) / K := by
    rw [div_le_div_iff₀ hw0 hKpos]
    nlinarith [mul_le_mul_of_nonneg_left hKw hf, mul_le_mul_of_nonneg_right hVr hw0.le]
  calc ENNReal.ofReal (α * f / w)
      ≤ ENNReal.ofReal (((bhReject α q ∩ H₀).card : ℝ) / K) := ENNReal.ofReal_le_ofReal hreal
    _ = ((bhReject α q ∩ H₀).card : ℝ≥0∞) / K := by
        rw [ENNReal.ofReal_div_of_pos hKpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-- The three count conditions together give the lower bound `α f / w` on the false discovery
proportion. -/
theorem fdp_bhReject_ge_of_bracket (hα : 0 < α) (q : ι → ℝ) (H₀ : Finset ι) {v w f : ℝ}
    (hv0 : 0 < v) (hv : v ≤ α) (hw0 : 0 < w) (hf : 0 ≤ f) {J : Type*} (lo hi : J → ℝ)
    (hcover : ∀ t, w < t → t ≤ α → ∃ j, lo j < t ∧ t ≤ hi j)
    (hcell : ∀ j, (cntLE univ q (hi j) : ℝ) < Fintype.card ι * lo j / α)
    (hcount : (Fintype.card ι : ℝ) * v / α + 1 ≤ cntLE univ q v)
    (hnull : (Fintype.card ι : ℝ) * f ≤ cntLE H₀ q v) :
    ENNReal.ofReal (α * f / w) ≤ fdp H₀ (bhReject α q) :=
  fdp_bhReject_ge_of_threshold hα q H₀ hv0 hw0 hf
    (le_bhThreshold_of_count hα q hv0.le hv hcount)
    (bhThreshold_le_of_cells hα q hw0.le lo hi hcover hcell) hnull

end Applied.MultipleTesting
