import Applied.Statistics.BenjaminiHochberg
import Applied.Statistics.Simes

/-!
# Benjamini–Hochberg under positive dependence (PRDS)

`IsPRDSOn P p H₀` says that the p-values are positively regression dependent on the true nulls
`H₀`, in the form used by Blanchard and Roquain (2008): for a true null `i` and an increasing
set `D` of p-value vectors, the conditional probability of `D` given `p i ≤ t` does not
decrease in `t`. It is written without division, so no conditioning on null events is needed.

`fdr_bhReject_le_of_prds`: under this condition the Benjamini–Hochberg procedure at level `α`
has false discovery rate at most `α m₀ / m` (Benjamini and Yekutieli 2001, Theorem 1.2).
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

/-- Algebraic core of the PRDS argument, by downward induction on `k`. Think of
`a k = P (p ≤ q k)`, `G k = P (K ≥ k, p ≤ q k)` and `H k = P (K ≥ k + 1, p ≤ q k)`. -/
lemma prds_core (m : ℕ) (c : ℝ) (hc : 0 ≤ c) (a G H : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (hamono : ∀ k, a k ≤ a (k + 1)) (hac : ∀ k, a k ≤ c * k)
    (hG : ∀ k, G k ≤ a k) (hH0 : ∀ k, 0 ≤ H k) (hHG : ∀ k, H k ≤ G k)
    (hprds : ∀ k, G (k + 1) * a k ≤ H k * a (k + 1)) :
    ∀ d k, k + d = m + 1 → 1 ≤ k →
      a k * (∑ j ∈ Ico k (m + 1), (G j - H j) / j) ≤ c * G k ∧
      ∑ j ∈ Ico k (m + 1), (G j - H j) / j ≤ c := by
  intro d
  induction d with
  | zero =>
    intro k hk _
    have : k = m + 1 := by omega
    subst this
    simp only [Finset.Ico_self, Finset.sum_empty, mul_zero]
    exact ⟨mul_nonneg hc ((hH0 _).trans (hHG _)), hc⟩
  | succ d ih =>
    intro k hk hk1
    obtain ⟨hC', hD'⟩ := ih (k + 1) (by omega) (by omega)
    have hkm : k < m + 1 := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hkm]
    set T' := ∑ j ∈ Ico (k + 1) (m + 1), (G j - H j) / j with hT'
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hGH : 0 ≤ G k - H k := sub_nonneg.mpr (hHG k)
    have ht0 : 0 ≤ (G k - H k) / k := div_nonneg hGH hkpos.le
    have h1 : a k * ((G k - H k) / k) ≤ c * (G k - H k) := by
      rw [mul_div_assoc', div_le_iff₀ hkpos]
      have := mul_le_mul_of_nonneg_right (hac k) hGH
      linarith
    have h2 : a k * T' ≤ c * H k := by
      rcases (ha0 (k + 1)).eq_or_lt with h0 | hpos
      · have hak : a k = 0 := le_antisymm (h0 ▸ hamono k) (ha0 k)
        rw [hak, zero_mul]; exact mul_nonneg hc (hH0 k)
      · refine le_of_mul_le_mul_right ?_ hpos
        calc a k * T' * a (k + 1) = a k * (a (k + 1) * T') := by ring
          _ ≤ a k * (c * G (k + 1)) := mul_le_mul_of_nonneg_left hC' (ha0 k)
          _ = c * (G (k + 1) * a k) := by ring
          _ ≤ c * (H k * a (k + 1)) := mul_le_mul_of_nonneg_left (hprds k) hc
          _ = c * H k * a (k + 1) := by ring
    have hC : a k * ((G k - H k) / k + T') ≤ c * G k := by
      rw [mul_add]; linarith
    refine ⟨hC, ?_⟩
    rcases (ha0 k).eq_or_lt with h0 | hpos
    · have hGk : G k - H k ≤ 0 := by have := hG k; have := hH0 k; linarith
      have : (G k - H k) / k ≤ 0 := div_nonpos_of_nonpos_of_nonneg hGk hkpos.le
      linarith
    · refine le_of_mul_le_mul_left ?_ hpos
      have := mul_le_mul_of_nonneg_left (hG k) hc
      linarith

variable {ι : Type*} [Fintype ι] {α : ℝ}

/-- Raising p-values can only lower the Benjamini–Hochberg cut-off. -/
lemma bhK_antitone {q q' : ι → ℝ} (h : q ≤ q') : bhK α q' ≤ bhK α q := by
  refine le_bhK q (bhK_le q') ((bhK_le_bhCount q').trans ?_)
  refine Finset.card_le_card fun j hj => ?_
  rw [mem_filter] at hj ⊢
  exact ⟨mem_univ _, (h j).trans hj.2⟩

variable [DecidableEq ι]

/-- Pointwise bound on the false discovery proportion in terms of the cut-off itself. -/
theorem fdp_bhReject_le_self (hα : 0 ≤ α) (H₀ : Finset ι) (q : ι → ℝ) :
    fdp H₀ (bhReject α q) ≤ ∑ i ∈ H₀, ∑ k ∈ Icc 1 (Fintype.card ι),
      if bhK α q = k ∧ q i ≤ α * k / Fintype.card ι then ((k : ℝ≥0∞))⁻¹ else 0 := by
  classical
  have hcard : ((bhReject α q ∩ H₀).card : ℝ≥0∞)
      = ∑ i ∈ H₀, if i ∈ bhReject α q then (1 : ℝ≥0∞) else 0 := by
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    push_cast
    rfl
  rw [fdp, hcard, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ bhReject α q
  · simp only [hi, ↓reduceIte, one_mul]
    have hmem : bhK α q ∈ Icc 1 (Fintype.card ι) :=
      mem_Icc.mpr ⟨one_le_bhK hα q hi, bhK_le q⟩
    have hterm : (if bhK α q = bhK α q ∧ q i ≤ α * (bhK α q : ℕ) / Fintype.card ι
        then ((bhK α q : ℝ≥0∞))⁻¹ else 0) = ((bhK α q : ℝ≥0∞))⁻¹ := by
      have hc : q i ≤ α * (bhK α q : ℕ) / Fintype.card ι := (mem_filter.mp hi).2
      simp only [hc, and_self, ↓reduceIte]
    calc ((bhReject α q).card : ℝ≥0∞)⁻¹ ≤ ((bhK α q : ℝ≥0∞))⁻¹ := by
          rw [ENNReal.inv_le_inv]; exact_mod_cast bhK_le_card_bhReject q
      _ = _ := hterm.symm
      _ ≤ _ := Finset.single_le_sum (f := fun k => if bhK α q = k ∧
            q i ≤ α * k / Fintype.card ι then ((k : ℝ≥0∞))⁻¹ else 0)
          (fun _ _ => zero_le) hmem
  · simp only [hi, ↓reduceIte, zero_mul]; exact zero_le

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Positive regression dependence on the subset `H₀` of true nulls, in the
conditioning-on-`p i ≤ t` form and cleared of denominators: for `i ∈ H₀`, an increasing
measurable set `D` of p-value vectors and `s ≤ t`,
`P (D, p i ≤ s) * P (p i ≤ t) ≤ P (D, p i ≤ t) * P (p i ≤ s)`. -/
def IsPRDSOn (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι) : Prop :=
  ∀ i ∈ H₀, ∀ D : Set (ι → ℝ), MeasurableSet D → IsUpperSet D → ∀ s t : ℝ, s ≤ t →
    P ((fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic s) * P (p i ⁻¹' Set.Iic t)
      ≤ P ((fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic t) * P (p i ⁻¹' Set.Iic s)

omit [Fintype ι] [DecidableEq ι] in
/-- The PRDS condition for decreasing sets, in real numbers. -/
lemma IsPRDSOn.lowerSet {P : Measure Ω} [IsProbabilityMeasure P] {p : ι → Ω → ℝ}
    {H₀ : Finset ι} (h : IsPRDSOn P p H₀) (hmeas : ∀ i, Measurable (p i))
    {i : ι} (hi : i ∈ H₀) {L : Set (ι → ℝ)} (hL : MeasurableSet L) (hlow : IsLowerSet L)
    {s t : ℝ} (hst : s ≤ t) :
    (P ((fun ω j => p j ω) ⁻¹' L ∩ p i ⁻¹' Set.Iic t)).toReal * (P (p i ⁻¹' Set.Iic s)).toReal
      ≤ (P ((fun ω j => p j ω) ⁻¹' L ∩ p i ⁻¹' Set.Iic s)).toReal
        * (P (p i ⁻¹' Set.Iic t)).toReal := by
  have hpm : Measurable fun ω j => p j ω := measurable_pi_iff.mpr hmeas
  have hLm : MeasurableSet ((fun ω j => p j ω) ⁻¹' L) := hpm hL
  have hup := h i hi Lᶜ hL.compl hlow.compl s t hst
  -- split each `{p i ≤ u}` into the parts inside and outside `L`
  have hsplit : ∀ u : ℝ, (P (p i ⁻¹' Set.Iic u)).toReal
      = (P ((fun ω j => p j ω) ⁻¹' L ∩ p i ⁻¹' Set.Iic u)).toReal
        + (P ((fun ω j => p j ω) ⁻¹' Lᶜ ∩ p i ⁻¹' Set.Iic u)).toReal := by
    intro u
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    congr 1
    rw [Set.inter_comm _ (p i ⁻¹' Set.Iic u), Set.inter_comm _ (p i ⁻¹' Set.Iic u),
      Set.preimage_compl]
    exact (measure_inter_add_sdiff₀ _ hLm.nullMeasurableSet).symm
  have hup' := ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    hup
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at hup'
  rw [hsplit s, hsplit t] at hup' ⊢
  ring_nf at hup' ⊢
  linarith

/-- **Benjamini–Hochberg under positive dependence.** If the p-values are valid under their
nulls and positively regression dependent on the set of true nulls, the Benjamini–Hochberg
procedure at level `α` has false discovery rate at most `α m₀ / m`. -/
theorem fdr_bhReject_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) (hprds : IsPRDSOn P p H₀) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) := by
  set m := Fintype.card ι with hm
  have hpm : Measurable fun ω j => p j ω := measurable_pi_iff.mpr hmeas
  set Kf : Ω → ℕ := fun ω => bhK α fun j => p j ω with hKf
  have hKm : Measurable Kf := measurable_bhK.comp hpm
  set q : ℕ → ℝ := fun k => α * k / m with hq
  have hq0 : ∀ k, 0 ≤ q k := fun k => by positivity
  have hqmono : ∀ k, q k ≤ q (k + 1) := by
    intro k; simp only [hq]; push_cast; gcongr; linarith
  -- lower sets `{x | k ≤ bhK α x}`
  set L : ℕ → Set (ι → ℝ) := fun k => {x | k ≤ bhK α x} with hLdef
  have hLm : ∀ k, MeasurableSet (L k) := fun k =>
    measurableSet_le measurable_const measurable_bhK
  have hLlow : ∀ k, IsLowerSet (L k) := fun k x y hyx hx =>
    le_trans (show k ≤ bhK α x from hx) (bhK_antitone hyx)
  have hone : ∀ i ∈ H₀, ∑ k ∈ Icc 1 m,
      ∫⁻ ω, (if Kf ω = k ∧ p i ω ≤ q k then ((k : ℝ≥0∞))⁻¹ else 0) ∂P
      ≤ ENNReal.ofReal (α / m) := by
    intro i hi
    set a : ℕ → ℝ := fun k => (P (p i ⁻¹' Set.Iic (q k))).toReal with ha
    set G : ℕ → ℝ := fun k =>
      (P ((fun ω j => p j ω) ⁻¹' L k ∩ p i ⁻¹' Set.Iic (q k))).toReal with hG
    set H : ℕ → ℝ := fun k =>
      (P ((fun ω j => p j ω) ⁻¹' L (k + 1) ∩ p i ⁻¹' Set.Iic (q k))).toReal with hH
    have hsub : ∀ k, (fun ω j => p j ω) ⁻¹' L (k + 1) ⊆ (fun ω j => p j ω) ⁻¹' L k :=
      fun k ω hω => Nat.le_of_succ_le (show k + 1 ≤ bhK α _ from hω)
    have hcore := prds_core m (α / m) (by positivity) a G H
      (fun k => ENNReal.toReal_nonneg)
      (fun k => ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (Set.preimage_mono (Set.Iic_subset_Iic.mpr (hqmono k)))))
      (fun k => by
        have h1 := hvalid i hi (q k) (hq0 k)
        have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
        rw [ENNReal.toReal_ofReal (hq0 k)] at h2
        have : q k = α / m * k := by simp only [hq]; ring
        exact (show a k ≤ q k from h2).trans (le_of_eq this))
      (fun k => ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_right))
      (fun k => ENNReal.toReal_nonneg)
      (fun k => ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (Set.inter_subset_inter_left _ (hsub k))))
      (fun k => hprds.lowerSet hmeas hi (hLm (k + 1)) (hLlow (k + 1)) (hqmono k))
    have hsum := (hcore m 1 (by omega) le_rfl).2
    -- each integral is `(G k - H k) / k`
    have hint : ∀ k ∈ Icc 1 m,
        ∫⁻ ω, (if Kf ω = k ∧ p i ω ≤ q k then ((k : ℝ≥0∞))⁻¹ else 0) ∂P
          = ENNReal.ofReal ((G k - H k) / k) := by
      intro k hk
      have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
      set Ek : Set Ω := ((fun ω j => p j ω) ⁻¹' L k ∩ p i ⁻¹' Set.Iic (q k))
        \ ((fun ω j => p j ω) ⁻¹' L (k + 1) ∩ p i ⁻¹' Set.Iic (q k)) with hEk
      have hA : MeasurableSet ((fun ω j => p j ω) ⁻¹' L k ∩ p i ⁻¹' Set.Iic (q k)) :=
        (hpm (hLm k)).inter (hmeas i measurableSet_Iic)
      have hB : MeasurableSet ((fun ω j => p j ω) ⁻¹' L (k + 1) ∩ p i ⁻¹' Set.Iic (q k)) :=
        (hpm (hLm (k + 1))).inter (hmeas i measurableSet_Iic)
      have hfun : (fun ω => if Kf ω = k ∧ p i ω ≤ q k then ((k : ℝ≥0∞))⁻¹ else 0)
          = Ek.indicator fun _ => ((k : ℝ≥0∞))⁻¹ := by
        funext ω
        by_cases h : Kf ω = k ∧ p i ω ≤ q k
        · have hmem : ω ∈ Ek := by
            refine ⟨⟨by simp [hLdef, hKf] at h ⊢; omega, h.2⟩, fun hcon => ?_⟩
            have : k + 1 ≤ Kf ω := hcon.1
            omega
          rw [Set.indicator_of_mem hmem]; simp [h.1, h.2]
        · have hmem : ω ∉ Ek := by
            rintro ⟨⟨hk', hp'⟩, hnot⟩
            have h1 : k ≤ Kf ω := hk'
            have h2 : ¬ (k + 1 ≤ Kf ω) := fun hc => hnot ⟨hc, hp'⟩
            exact h ⟨by omega, hp'⟩
          rw [Set.indicator_of_notMem hmem]; simp only [h, ↓reduceIte]
      have hPE : P Ek = ENNReal.ofReal (G k - H k) := by
        rw [hEk, measure_sdiff (Set.inter_subset_inter_left _ (hsub k)) hB.nullMeasurableSet
          (measure_ne_top _ _), ← ENNReal.ofReal_toReal (measure_ne_top P _),
          ← ENNReal.ofReal_toReal (measure_ne_top P
            ((fun ω j => p j ω) ⁻¹' L (k + 1) ∩ p i ⁻¹' Set.Iic (q k))),
          ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
      rw [hfun, lintegral_indicator_const (hA.diff hB), hPE,
        ← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_inv_of_pos hkpos,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1; field_simp
    rw [Finset.sum_congr rfl hint,
      ← ENNReal.ofReal_sum_of_nonneg fun k hk => div_nonneg (sub_nonneg.mpr
        (ENNReal.toReal_mono (measure_ne_top _ _)
          (measure_mono (Set.inter_subset_inter_left _ (hsub k))))) (Nat.cast_nonneg k)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hIcc : Icc 1 m = Ico 1 (m + 1) := by ext k; simp
    rw [hIcc]; exact hsum
  have hFmeas : ∀ i k, Measurable fun ω =>
      (if Kf ω = k ∧ p i ω ≤ q k then ((k : ℝ≥0∞))⁻¹ else 0) := by
    intro i k
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (hKm (measurableSet_singleton k)).inter (hmeas i measurableSet_Iic)
  calc fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ∫⁻ ω, ∑ i ∈ H₀, ∑ k ∈ Icc 1 m,
          (if Kf ω = k ∧ p i ω ≤ q k then ((k : ℝ≥0∞))⁻¹ else 0) ∂P :=
        lintegral_mono fun ω => fdp_bhReject_le_self hα H₀ _
    _ = ∑ i ∈ H₀, ∑ k ∈ Icc 1 m,
          ∫⁻ ω, (if Kf ω = k ∧ p i ω ≤ q k then ((k : ℝ≥0∞))⁻¹ else 0) ∂P := by
        rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun k _ => hFmeas i k]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ fun k _ => hFmeas i k]
    _ ≤ ∑ _i ∈ H₀, ENNReal.ofReal (α / m) := Finset.sum_le_sum hone
    _ = ENNReal.ofReal (α * H₀.card / m) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast H₀.card,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1; ring

/-- **Simes inequality under positive dependence.** If all hypotheses are true nulls whose
p-values are valid and PRDS, the Simes test rejects with probability at most `α`. -/
theorem measure_one_le_bhK_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i))
    (hvalid : ∀ i, IsValidPValue P (p i)) (hprds : IsPRDSOn P p univ) :
    P {ω | 1 ≤ bhK α fun j => p j ω} ≤ ENNReal.ofReal α := by
  refine (measure_one_le_bhK_le_fdr P p hmeas).trans
    ((fdr_bhReject_le_of_prds P hα p hmeas univ (fun i _ => hvalid i) hprds).trans
      (ENNReal.ofReal_le_ofReal ?_))
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · simp [h0, hα]
  · have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hpos
    rw [Finset.card_univ, mul_div_assoc, div_self hm.ne', mul_one]

/-- **Hommel's procedure under positive dependence.** It is enough that the p-values of the
true nulls, as a family on their own, are valid and PRDS. -/
theorem fwer_hommel_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hprds : IsPRDSOn P (fun j : H₀ => p j) univ) :
    fwer P H₀ (hommel α p) ≤ ENNReal.ofReal α :=
  fwer_closedTest_le P _ H₀ _
    (measure_one_le_bhK_le_of_prds P hα (fun j : H₀ => p j) (fun j => hmeas j)
      (fun j => hvalid j j.2) hprds)

/-- **Hochberg's procedure under positive dependence.** -/
theorem fwer_hochberg_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hprds : IsPRDSOn P (fun j : H₀ => p j) univ) :
    fwer P H₀ (hochberg α p) ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans (fwer_hommel_le_of_prds P hα p hmeas H₀ hvalid hprds)
  rintro ω ⟨i, hi, hrej⟩
  exact ⟨i, hi, hochberg_subset_hommel hα p ω hrej⟩

end Applied.MultipleTesting
