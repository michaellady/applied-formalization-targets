import Applied.Statistics.Simes
import Applied.Statistics.BHMonotone
import Applied.Statistics.SidakExact

/-!
# Exactness of the Benjamini–Hochberg bound and of the Simes test

For independent p-values that are exactly uniform on `[0, 1]` under the null hypotheses, the
two classical inequalities of the Simes family become equalities.

* `fdr_bhReject_eq` (Benjamini and Hochberg 1995; Benjamini and Yekutieli 2001): if each
  true-null p-value is exactly uniform and independent of the vector of the other p-values,
  the Benjamini–Hochberg procedure at level `α ∈ [0, 1]` has false discovery rate exactly
  `α m₀ / m`.
* `measure_one_le_bhK_eq` (**Simes 1986 identity**): under the global null, with at least one
  hypothesis and mutually independent, exactly uniform p-values, the Simes test (reject when
  `p₍ₖ₎ ≤ α k / m` for some `k`) rejects with probability exactly `α`, for `α ∈ [0, 1]`.
  `measure_simesLocal_eq` is the same statement for the Simes test of a non-empty set of true
  nulls.

The proof follows the leave-one-out argument of `fdr_bhReject_le`, with every inequality
replaced by an equality: `fdp_bhReject_eq` is an exact pointwise decomposition of the false
discovery proportion (`mem_bhReject_of_le_update` is the converse of `bhK_update_eq`), the
exact uniform distribution gives `P (p i ≤ α k / m) = α k / m`, and the leave-one-out cut-off
always lies in `[1, m]`.

"Exactly uniform" is `IsUniformPValue` (distribution function `t ↦ t` on `[0, 1]`); it is
used only at the points `α k / m`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ}

section Deterministic

/-- Lowering one p-value to zero can only raise the Benjamini–Hochberg cut-off. -/
lemma bhK_le_bhK_update (hα : 0 ≤ α) (q : ι → ℝ) (i : ι) :
    bhK α q ≤ bhK α (Function.update q i 0) := by
  have hmono : ∀ k, bhCount α q k ≤ bhCount α (Function.update q i 0) k := by
    intro k
    refine Finset.card_le_card fun j hj => ?_
    rw [mem_filter] at hj ⊢
    refine ⟨mem_univ _, ?_⟩
    by_cases hji : j = i
    · subst hji
      have : (0 : ℝ) ≤ α * k / Fintype.card ι := by positivity
      simpa using this
    · simpa [Function.update_of_ne hji] using hj.2
  exact le_bhK _ (bhK_le q) ((bhK_le_bhCount q).trans (hmono _))

/-- **Converse of the leave-one-out lemma.** If `q i` is below the threshold of the
leave-one-out cut-off, then `i` is rejected and the cut-off is unchanged. -/
lemma mem_bhReject_of_le_update (hα : 0 ≤ α) (q : ι → ℝ) (i : ι)
    (h : q i ≤ α * bhK α (Function.update q i 0) / Fintype.card ι) :
    i ∈ bhReject α q ∧ bhK α q = bhK α (Function.update q i 0) := by
  set k' := bhK α (Function.update q i 0) with hk'
  have hthr : (0 : ℝ) ≤ α * k' / Fintype.card ι := by positivity
  have heq : bhCount α (Function.update q i 0) k' = bhCount α q k' := by
    unfold bhCount
    congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and]
    by_cases hji : j = i
    · subst hji; simpa using ⟨fun _ => h, fun _ => hthr⟩
    · simp [Function.update_of_ne hji]
  have hk'count : k' ≤ bhCount α q k' := heq ▸ bhK_le_bhCount _
  have hge : k' ≤ bhK α q := le_bhK q (bhK_le _) hk'count
  have hK : bhK α q = k' := le_antisymm (bhK_le_bhK_update hα q i) hge
  refine ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, hK⟩
  rw [hK]; exact h

/-- **Exact pointwise decomposition of the false discovery proportion** of
Benjamini–Hochberg: each true null `i` contributes `1 / k` exactly on the event that the
leave-one-out cut-off equals `k` and `q i ≤ α k / m`. -/
theorem fdp_bhReject_eq (hα : 0 ≤ α) (H₀ : Finset ι) (q : ι → ℝ) :
    fdp H₀ (bhReject α q) = ∑ i ∈ H₀, ∑ k ∈ Icc 1 (Fintype.card ι),
      if bhK α (Function.update q i 0) = k ∧ q i ≤ α * k / Fintype.card ι
        then ((k : ℝ≥0∞))⁻¹ else 0 := by
  classical
  have hcard : ((bhReject α q ∩ H₀).card : ℝ≥0∞)
      = ∑ i ∈ H₀, if i ∈ bhReject α q then (1 : ℝ≥0∞) else 0 := by
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    push_cast
    rfl
  rw [fdp, hcard, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ bhReject α q
  · simp only [hi, ↓reduceIte, one_mul]
    have h1 : 1 ≤ bhK α q := one_le_bhK hα q hi
    have hmem : bhK α q ∈ Icc 1 (Fintype.card ι) := mem_Icc.mpr ⟨h1, bhK_le q⟩
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · have hc : bhK α (Function.update q i 0) = bhK α q ∧
          q i ≤ α * (bhK α q : ℕ) / Fintype.card ι :=
        ⟨bhK_update_eq hα q i hi, (mem_filter.mp hi).2⟩
      simp only [hc, and_self, ↓reduceIte, card_bhReject hα q]
    · intro k _ hk
      have : ¬ (bhK α (Function.update q i 0) = k) := by
        rw [bhK_update_eq hα q i hi]; exact fun h => hk h.symm
      simp [this]
  · simp only [hi, ↓reduceIte, zero_mul]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    have : ¬ (bhK α (Function.update q i 0) = k ∧ q i ≤ α * k / Fintype.card ι) := by
      rintro ⟨hk, hqi⟩
      subst hk
      exact hi (mem_bhReject_of_le_update hα q i hqi).1
    simp only [this, ↓reduceIte]

/-- The leave-one-out cut-off is at least one (for `α ≥ 0`). -/
lemma one_le_bhK_update (hα : 0 ≤ α) (q : ι → ℝ) (i : ι) :
    1 ≤ bhK α (Function.update q i 0) := by
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  refine le_bhK _ hcard (Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩)
  simp only [Function.update_self, Nat.cast_one, mul_one]
  positivity

/-- Under the global null the false discovery proportion of Benjamini–Hochberg is the
indicator that the Simes test rejects. -/
lemma fdp_univ_bhReject (hα : 0 ≤ α) (q : ι → ℝ) :
    fdp univ (bhReject α q) = if 1 ≤ bhK α q then 1 else 0 := by
  by_cases h : 1 ≤ bhK α q
  · have hne := bhReject_nonempty_of_one_le_bhK _ h
    have hcard : ((bhReject α q).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hne).ne'
    rw [ite_eq_left h, fdp, Finset.inter_univ, ENNReal.div_self hcard (ENNReal.natCast_ne_top _)]
  · have hempty : bhReject α q = ∅ :=
      Finset.eq_empty_of_forall_notMem fun i hi => h (one_le_bhK hα q hi)
    rw [ite_eq_right h, fdp, hempty]
    simp

end Deterministic

section Probabilistic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Benjamini–Hochberg bound is exact.** If each true-null p-value is exactly uniform on
`[0, 1]` and independent of the vector of the other p-values, the Benjamini–Hochberg procedure
at level `α ∈ [0, 1]` has false discovery rate exactly `α m₀ / m`. -/
theorem fdr_bhReject_eq (P : Measure Ω) [IsProbabilityMeasure P] (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hunif : ∀ i ∈ H₀, IsUniformPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      = ENNReal.ofReal (α * H₀.card / Fintype.card ι) := by
  set m := Fintype.card ι with hm
  set Y : ι → Ω → ι → ℝ := fun i ω => Function.update (fun j => p j ω) i 0 with hY
  have hYmeas : ∀ i, Measurable (Y i) := by
    intro i
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hji : j = i
    · subst hji; simp [hY]
    · simpa [hY, Function.update_of_ne hji] using hmeas j
  set A : ι → ℕ → Set Ω := fun i k => Y i ⁻¹' {q | bhK α q = k} with hA
  set B : ι → ℕ → Set Ω := fun i k => p i ⁻¹' Set.Iic (α * k / m) with hB
  have hSk : ∀ k : ℕ, MeasurableSet {q : ι → ℝ | bhK α q = k} := fun k =>
    measurable_bhK (measurableSet_singleton k)
  have hAmeas : ∀ i k, MeasurableSet (A i k) := fun i k => hYmeas i (hSk k)
  have hBmeas : ∀ i k, MeasurableSet (B i k) := fun i k => hmeas i measurableSet_Iic
  -- the contribution of a single true null and a single value of the cut-off, exactly
  have hterm : ∀ i ∈ H₀, ∀ k ∈ Icc 1 m,
      ∫⁻ ω, (if bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m then ((k : ℝ≥0∞))⁻¹ else 0) ∂P
        = ENNReal.ofReal (α / m) * P (A i k) := by
    intro i hi k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hkm : k ≤ m := (mem_Icc.mp hk).2
    have hfun : (fun ω => if bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m then ((k : ℝ≥0∞))⁻¹ else 0)
        = (B i k ∩ A i k).indicator fun _ => ((k : ℝ≥0∞))⁻¹ := by
      funext ω
      by_cases h : bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m
      · have hmem : ω ∈ B i k ∩ A i k := ⟨h.2, h.1⟩
        rw [Set.indicator_of_mem hmem]; simp [h.1, h.2]
      · have hmem : ω ∉ B i k ∩ A i k := fun hmem => h ⟨hmem.2, hmem.1⟩
        rw [Set.indicator_of_notMem hmem]; simp only [h, ↓reduceIte]
    rw [hfun, lintegral_indicator_const ((hBmeas i k).inter (hAmeas i k))]
    have hprod : P (B i k ∩ A i k) = P (B i k) * P (A i k) :=
      (hindep i hi).measure_inter_preimage_eq_mul _ _ measurableSet_Iic (hSk k)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.lt_of_lt_of_le hk1 hkm)
    have ht0 : 0 ≤ α * k / m := by positivity
    have ht1 : α * k / m ≤ 1 := by
      rw [div_le_one hmpos]
      have : (k : ℝ) ≤ m := by exact_mod_cast hkm
      nlinarith
    have hBeq : P (B i k) = ENNReal.ofReal (α * k / m) := hunif i hi _ ht0 ht1
    have hkne : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
    have hsplit : ENNReal.ofReal (α * k / m) = (k : ℝ≥0∞) * ENNReal.ofReal (α / m) := by
      rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
      congr 1; ring
    rw [hprod, hBeq, hsplit, ← mul_assoc, ← mul_assoc,
      ENNReal.inv_mul_cancel hkne (ENNReal.natCast_ne_top k), one_mul]
  -- the events `A i k`, `k ∈ [1, m]`, partition the sample space
  have hsumA : ∀ i, ∑ k ∈ Icc 1 m, P (A i k) = 1 := by
    intro i
    rw [← measure_biUnion_finset (fun k _ l _ hkl => ?_) (fun k _ => hAmeas i k)]
    · have huniv : (⋃ k ∈ Icc 1 m, A i k) = Set.univ := by
        refine Set.eq_univ_of_forall fun ω => Set.mem_biUnion (x := bhK α (Y i ω)) ?_ rfl
        exact mem_Icc.mpr ⟨one_le_bhK_update hα0 _ i, bhK_le _⟩
      rw [huniv, measure_univ]
    · rw [Function.onFun, Set.disjoint_left]
      rintro ω hk' hl'
      exact hkl (hk'.symm.trans hl')
  have hFmeas : ∀ i k, Measurable fun ω =>
      (if bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m then ((k : ℝ≥0∞))⁻¹ else 0) := by
    intro i k
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (hAmeas i k).inter (hBmeas i k)
  calc fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      = ∫⁻ ω, ∑ i ∈ H₀, ∑ k ∈ Icc 1 m,
          (if bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m then ((k : ℝ≥0∞))⁻¹ else 0) ∂P :=
        lintegral_congr fun ω => fdp_bhReject_eq hα0 H₀ _
    _ = ∑ i ∈ H₀, ∑ k ∈ Icc 1 m,
          ∫⁻ ω, (if bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m then ((k : ℝ≥0∞))⁻¹ else 0) ∂P := by
        rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun k _ => hFmeas i k]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ fun k _ => hFmeas i k]
    _ = ∑ i ∈ H₀, ∑ k ∈ Icc 1 m, ENNReal.ofReal (α / m) * P (A i k) :=
        Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => hterm i hi k hk
    _ = ∑ i ∈ H₀, ENNReal.ofReal (α / m) * ∑ k ∈ Icc 1 m, P (A i k) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ _i ∈ H₀, ENNReal.ofReal (α / m) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsumA i, mul_one]
    _ = ENNReal.ofReal (α * H₀.card / m) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast H₀.card,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1; ring

/-- **Simes identity (Simes 1986).** Under the global null, with at least one hypothesis and
mutually independent p-values that are exactly uniform on `[0, 1]`, the Simes test rejects
(`p₍ₖ₎ ≤ α k / m` for some `k ≥ 1`, i.e. `1 ≤ bhK α p`) with probability exactly `α`, for
`0 ≤ α ≤ 1`. -/
theorem measure_one_le_bhK_eq [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i))
    (hindep : iIndepFun p P) (hunif : ∀ i, IsUniformPValue P (p i)) :
    P {ω | 1 ≤ bhK α fun j => p j ω} = ENNReal.ofReal α := by
  have hpm : Measurable fun ω => (fun j => p j ω) := measurable_pi_iff.mpr hmeas
  have hS : MeasurableSet {ω | 1 ≤ bhK α fun j => p j ω} := by
    have h := (measurable_bhK (α := α)).comp hpm
    have hset : {ω | 1 ≤ bhK α fun j => p j ω}
        = (fun ω => bhK α fun j => p j ω) ⁻¹' {0}ᶜ := by
      ext ω; simp [Nat.one_le_iff_ne_zero]
    rw [hset]; exact h (measurableSet_singleton 0).compl
  have hfdr := fdr_bhReject_eq P hα0 hα1 p hmeas univ (fun i _ => hunif i)
    fun i _ => indepFun_update_of_iIndepFun P p hmeas hindep i
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [card_univ, mul_div_assoc, div_self hm.ne', mul_one] at hfdr
  rw [← hfdr, fdr, ← lintegral_indicator_one hS]
  refine lintegral_congr fun ω => ?_
  rw [fdp_univ_bhReject hα0]
  by_cases h : 1 ≤ bhK α fun j => p j ω
  · rw [ite_eq_left h, Set.indicator_of_mem (by exact h)]; rfl
  · rw [ite_eq_right h, Set.indicator_of_notMem (by exact h)]

omit [Fintype ι] in
/-- **Simes identity for a set of true nulls.** If the p-values are mutually independent and
the true-null ones (a non-empty set `H₀`) are exactly uniform on `[0, 1]`, the Simes test of
`H₀` rejects with probability exactly `α`, for `0 ≤ α ≤ 1`. -/
theorem measure_simesLocal_eq (P : Measure Ω) [IsProbabilityMeasure P] (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P)
    (H₀ : Finset ι) (hne : H₀.Nonempty) (hunif : ∀ i ∈ H₀, IsUniformPValue P (p i)) :
    P {ω | simesLocal α p H₀ ω} = ENNReal.ofReal α := by
  have : Nonempty H₀ := hne.to_subtype
  exact measure_one_le_bhK_eq P hα0 hα1 (fun j : H₀ => p j) (fun j => hmeas j)
    (hindep.precomp Subtype.val_injective) fun j => hunif j j.2

end Probabilistic

end Applied.MultipleTesting
