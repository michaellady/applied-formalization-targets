import Applied.Statistics.MultipleTesting
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The Benjamini–Hochberg procedure

The step-up procedure of Benjamini and Hochberg (1995) and its false discovery rate under
independence. Notation as in `Applied.Statistics.MultipleTesting`; `m₀ = |H₀|` is the number of
true nulls.

## Deterministic part

For a vector of p-values `q : ι → ℝ` with `m = |ι|`:

* `bhCount α q k`: how many p-values are at most `α k / m`.
* `bhK α q`: the largest `k ≤ m` with at least `k` p-values at most `α k / m`.
* `bhReject α q`: the rejected hypotheses, those with `q j ≤ α (bhK α q) / m`.
* `bhK_update_eq`: the leave-one-out lemma. If hypothesis `i` is rejected, setting its p-value
  to zero does not change the number of rejections.
* `fdp H₀ R`: the false discovery proportion `|R ∩ H₀| / |R|` of a rejection set (`0 / 0 = 0`).
* `fdp_bhReject_le`: pointwise bound on the false discovery proportion.

## Probabilistic part

* `fdr P H₀ R`: the false discovery rate, the expectation of `fdp H₀ (R ω)`.
* `fdr_bhReject_le`: the **Benjamini–Hochberg theorem**. If every true-null p-value is valid and
  independent of the vector of the other p-values, the procedure at level `α ≥ 0` has false
  discovery rate at most `α m₀ / m`. All p-values are assumed measurable; nothing else is
  assumed about the false nulls or about dependence among them.
* `fdr_bhReject_le_of_iIndepFun`: the textbook corollary for mutually independent p-values,
  with the bound `α`.

## Conventions

`bhReject` is written without sorting; `bhSorted_eq_bhReject` in
`Applied.Statistics.SortedProcedures` proves that it agrees with the textbook step-up rule on
sorted p-values (for `α ≥ 0`, any tie-breaking). `fdr_bhReject_eq` in
`Applied.Statistics.SimesExact` shows that the bound `α m₀ / m` is attained for exactly uniform
independent null p-values and levels `0 ≤ α ≤ 1`.

## Related files

* `BHMonotone`: the number of rejections equals `bhK`; monotonicity in the p-values.
* `BenjaminiYekutieli`: arbitrary dependence, with the harmonic factor.
* `PRDS`: positive dependence, with the same bound `α m₀ / m`.
* `Simes`: the Simes test is the event `1 ≤ bhK α q`.
* `StepUpAdjusted`: Benjamini–Hochberg-adjusted p-values.

## Not in this file

Adaptive procedures that estimate `m₀` (Storey; Benjamini–Krieger–Yekutieli), weighted
Benjamini–Hochberg, and control of the false discovery proportion in probability.
-/

open Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {ι : Type*} [Fintype ι]

section Deterministic

variable (α : ℝ)

/-- Number of p-values at most `α k / m`. -/
noncomputable def bhCount (q : ι → ℝ) (k : ℕ) : ℕ :=
  (univ.filter fun j => q j ≤ α * k / Fintype.card ι).card

/-- The Benjamini–Hochberg cut-off index: the largest `k ≤ m` such that at least `k` p-values
are at most `α k / m` (zero if there is none). -/
noncomputable def bhK (q : ι → ℝ) : ℕ :=
  (range (Fintype.card ι + 1)).sup fun k => if k ≤ bhCount α q k then k else 0

/-- The hypotheses rejected by the Benjamini–Hochberg procedure at level `α`. -/
noncomputable def bhReject (q : ι → ℝ) : Finset ι :=
  univ.filter fun j => q j ≤ α * bhK α q / Fintype.card ι

/-- False discovery proportion of a rejection set `R` when `H₀` are the true nulls
(`0 / 0 = 0`). -/
noncomputable def fdp [DecidableEq ι] (H₀ R : Finset ι) : ℝ≥0∞ :=
  ((R ∩ H₀).card : ℝ≥0∞) / R.card

variable {α}

/-- The cut-off index is at most the number `m` of hypotheses. -/
lemma bhK_le (q : ι → ℝ) : bhK α q ≤ Fintype.card ι := by
  refine Finset.sup_le fun k hk => ?_
  have : k ≤ Fintype.card ι := Nat.lt_succ_iff.mp (mem_range.mp hk)
  split_ifs <;> omega

/-- At the cut-off `k = bhK α q`, at least `k` p-values are at most `α k / m`. -/
lemma bhK_le_bhCount (q : ι → ℝ) : bhK α q ≤ bhCount α q (bhK α q) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup (range (Fintype.card ι + 1)) nonempty_range_add_one
    (fun k => if k ≤ bhCount α q k then k else 0)
  have hk' : bhK α q = if k ≤ bhCount α q k then k else 0 := hk
  by_cases h : k ≤ bhCount α q k
  · simp only [h, ↓reduceIte] at hk'
    rw [hk']; exact h
  · simp only [h, ↓reduceIte] at hk'
    rw [hk']; exact Nat.zero_le _

/-- Any `k ≤ m` such that at least `k` p-values are at most `α k / m` is at most the cut-off. -/
lemma le_bhK (q : ι → ℝ) {k : ℕ} (hk : k ≤ Fintype.card ι) (h : k ≤ bhCount α q k) :
    k ≤ bhK α q := by
  have h1 : k = (fun k => if k ≤ bhCount α q k then k else 0) k := by simp [h]
  exact h1.le.trans (Finset.le_sup (f := fun k => if k ≤ bhCount α q k then k else 0)
    (mem_range.mpr (Nat.lt_succ_iff.mpr hk)))

/-- The procedure rejects at least `bhK α q` hypotheses (exactly that many for `α ≥ 0`:
`card_bhReject` in `Applied.Statistics.BHMonotone`). -/
lemma bhK_le_card_bhReject (q : ι → ℝ) : bhK α q ≤ (bhReject α q).card :=
  bhK_le_bhCount q

/-- A rejected hypothesis forces at least one rejection to be counted. -/
lemma one_le_bhK (hα : 0 ≤ α) (q : ι → ℝ) {i : ι} (hi : i ∈ bhReject α q) : 1 ≤ bhK α q := by
  by_contra hlt
  have h0 : bhK α q = 0 := by omega
  have hqi : q i ≤ 0 := by
    have := (mem_filter.mp hi).2
    simpa [h0] using this
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hcount : 1 ≤ bhCount α q 1 := by
    refine Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hqi.trans ?_⟩⟩
    positivity
  have := le_bhK q hcard hcount
  omega

variable [DecidableEq ι]

/-- **Leave-one-out lemma.** If hypothesis `i` is rejected, replacing its p-value by zero
leaves the Benjamini–Hochberg cut-off unchanged. -/
lemma bhK_update_eq (hα : 0 ≤ α) (q : ι → ℝ) (i : ι) (hi : i ∈ bhReject α q) :
    bhK α (Function.update q i 0) = bhK α q := by
  have hqi : q i ≤ α * bhK α q / Fintype.card ι := (mem_filter.mp hi).2
  have hthr : ∀ k : ℕ, (0 : ℝ) ≤ α * k / Fintype.card ι := fun k => by positivity
  -- lowering a p-value can only increase the counts
  have hmono : ∀ k, bhCount α q k ≤ bhCount α (Function.update q i 0) k := by
    intro k
    refine Finset.card_le_card fun j hj => ?_
    rw [mem_filter] at hj ⊢
    refine ⟨mem_univ _, ?_⟩
    by_cases hji : j = i
    · subst hji; simpa using hthr k
    · simpa [Function.update_of_ne hji] using hj.2
  apply le_antisymm
  · -- any larger candidate cut-off for the updated vector also works for `q`
    by_contra hlt
    rw [not_le] at hlt
    set k' := bhK α (Function.update q i 0) with hk'
    have hk'le : k' ≤ Fintype.card ι := bhK_le _
    have hk'count : k' ≤ bhCount α (Function.update q i 0) k' := bhK_le_bhCount _
    have hqi' : q i ≤ α * k' / Fintype.card ι := by
      refine hqi.trans ?_
      have : (bhK α q : ℝ) ≤ k' := by exact_mod_cast hlt.le
      gcongr
    have heq : bhCount α (Function.update q i 0) k' = bhCount α q k' := by
      unfold bhCount
      congr 1
      ext j
      simp only [mem_filter, mem_univ, true_and]
      by_cases hji : j = i
      · subst hji; simpa using ⟨fun _ => hqi', fun _ => hthr k'⟩
      · simp [Function.update_of_ne hji]
    rw [heq] at hk'count
    have := le_bhK q hk'le hk'count
    omega
  · exact le_bhK _ (bhK_le q) ((bhK_le_bhCount q).trans (hmono _))

/-- Pointwise bound on the false discovery proportion of Benjamini–Hochberg: each true null
`i` contributes at most `1 / k` on the event that the leave-one-out cut-off equals `k` and
`q i ≤ α k / m`. -/
theorem fdp_bhReject_le (hα : 0 ≤ α) (H₀ : Finset ι) (q : ι → ℝ) :
    fdp H₀ (bhReject α q) ≤ ∑ i ∈ H₀, ∑ k ∈ Icc 1 (Fintype.card ι),
      if bhK α (Function.update q i 0) = k ∧ q i ≤ α * k / Fintype.card ι
        then ((k : ℝ≥0∞))⁻¹ else 0 := by
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
    have h1 : 1 ≤ bhK α q := one_le_bhK hα q hi
    have hmem : bhK α q ∈ Icc 1 (Fintype.card ι) := mem_Icc.mpr ⟨h1, bhK_le q⟩
    have hterm : (if bhK α (Function.update q i 0) = bhK α q ∧
        q i ≤ α * (bhK α q : ℕ) / Fintype.card ι then ((bhK α q : ℝ≥0∞))⁻¹ else 0)
        = ((bhK α q : ℝ≥0∞))⁻¹ := by
      have hc : bhK α (Function.update q i 0) = bhK α q ∧
          q i ≤ α * (bhK α q : ℕ) / Fintype.card ι :=
        ⟨bhK_update_eq hα q i hi, (mem_filter.mp hi).2⟩
      simp only [hc, and_self, ↓reduceIte]
    calc ((bhReject α q).card : ℝ≥0∞)⁻¹ ≤ ((bhK α q : ℝ≥0∞))⁻¹ := by
          rw [ENNReal.inv_le_inv]; exact_mod_cast bhK_le_card_bhReject q
      _ = _ := hterm.symm
      _ ≤ _ := Finset.single_le_sum (f := fun k => if bhK α (Function.update q i 0) = k ∧
            q i ≤ α * k / Fintype.card ι then ((k : ℝ≥0∞))⁻¹ else 0)
          (fun _ _ => zero_le) hmem
  · simp only [hi, ↓reduceIte, zero_mul]; exact zero_le

end Deterministic

section Probabilistic

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] [DecidableEq ι] {α : ℝ}

/-- False discovery rate: the expected false discovery proportion. -/
noncomputable def fdr (P : Measure Ω) (H₀ : Finset ι) (R : Ω → Finset ι) : ℝ≥0∞ :=
  ∫⁻ ω, fdp H₀ (R ω) ∂P

omit [DecidableEq ι] in
/-- The count `bhCount α q k` is a measurable function of the vector of p-values. -/
lemma measurable_bhCount (k : ℕ) : Measurable fun q : ι → ℝ => bhCount α q k := by
  classical
  have : (fun q : ι → ℝ => bhCount α q k)
      = fun q => ∑ j, if q j ≤ α * k / Fintype.card ι then 1 else 0 := by
    funext q; rw [bhCount, Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (measurableSet_le (measurable_pi_apply j) measurable_const)
      measurable_const measurable_const

omit [DecidableEq ι] in
/-- The cut-off index `bhK α q` is a measurable function of the vector of p-values. -/
lemma measurable_bhK : Measurable fun q : ι → ℝ => bhK α q := by
  have hterm : ∀ k : ℕ, Measurable fun q : ι → ℝ => if k ≤ bhCount α q k then k else 0 :=
    fun k => Measurable.ite (measurableSet_le measurable_const (measurable_bhCount k))
      measurable_const measurable_const
  have : ∀ n : ℕ, Measurable fun q : ι → ℝ =>
      (range n).sup fun k => if k ≤ bhCount α q k then k else 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.range_add_one, Finset.sup_insert]
      exact (hterm n).sup ih
  exact this _

/-- **Benjamini–Hochberg theorem.** If every true-null p-value is valid and independent of the
other p-values, the Benjamini–Hochberg procedure at level `α` has false discovery rate at most
`α m₀ / m`, where `m₀` is the number of true nulls. -/
theorem fdr_bhReject_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) := by
  set m := Fintype.card ι with hm
  -- the leave-one-out p-value vectors and their measurability
  set Y : ι → Ω → ι → ℝ := fun i ω => Function.update (fun j => p j ω) i 0 with hY
  have hYmeas : ∀ i, Measurable (Y i) := by
    intro i
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hji : j = i
    · subst hji; simp [hY]
    · simpa [hY, Function.update_of_ne hji] using hmeas j
  -- events
  set A : ι → ℕ → Set Ω := fun i k => Y i ⁻¹' {q | bhK α q = k} with hA
  set B : ι → ℕ → Set Ω := fun i k => p i ⁻¹' Set.Iic (α * k / m) with hB
  have hSk : ∀ k : ℕ, MeasurableSet {q : ι → ℝ | bhK α q = k} := fun k =>
    measurable_bhK (measurableSet_singleton k)
  have hAmeas : ∀ i k, MeasurableSet (A i k) := fun i k => hYmeas i (hSk k)
  have hBmeas : ∀ i k, MeasurableSet (B i k) := fun i k => hmeas i measurableSet_Iic
  -- the contribution of a single true null and a single value of the cut-off
  have hterm : ∀ i ∈ H₀, ∀ k ∈ Icc 1 m,
      ∫⁻ ω, (if bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m then ((k : ℝ≥0∞))⁻¹ else 0) ∂P
        ≤ ENNReal.ofReal (α / m) * P (A i k) := by
    intro i hi k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
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
    have hBle : P (B i k) ≤ ENNReal.ofReal (α * k / m) :=
      hvalid i hi _ (by positivity)
    have hkne : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
    have hsplit : ENNReal.ofReal (α * k / m) = (k : ℝ≥0∞) * ENNReal.ofReal (α / m) := by
      rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
      congr 1; ring
    calc ((k : ℝ≥0∞))⁻¹ * P (B i k ∩ A i k)
        = ((k : ℝ≥0∞))⁻¹ * (P (B i k) * P (A i k)) := by rw [hprod]
      _ ≤ ((k : ℝ≥0∞))⁻¹ * (((k : ℝ≥0∞) * ENNReal.ofReal (α / m)) * P (A i k)) := by
          rw [← hsplit]; gcongr
      _ = ENNReal.ofReal (α / m) * P (A i k) := by
          rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hkne (ENNReal.natCast_ne_top k),
            one_mul]
  -- the events `A i k` for different `k` are disjoint
  have hsumA : ∀ i, ∑ k ∈ Icc 1 m, P (A i k) ≤ 1 := by
    intro i
    rw [← measure_biUnion_finset (fun k _ l _ hkl => ?_) (fun k _ => hAmeas i k)]
    · exact prob_le_one
    · rw [Function.onFun, Set.disjoint_left]
      rintro ω hk' hl'
      exact hkl (hk'.symm.trans hl')
  have hFmeas : ∀ i k, Measurable fun ω =>
      (if bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m then ((k : ℝ≥0∞))⁻¹ else 0) := by
    intro i k
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (hAmeas i k).inter (hBmeas i k)
  calc fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ∫⁻ ω, ∑ i ∈ H₀, ∑ k ∈ Icc 1 m,
          (if bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m then ((k : ℝ≥0∞))⁻¹ else 0) ∂P :=
        lintegral_mono fun ω => fdp_bhReject_le hα H₀ _
    _ = ∑ i ∈ H₀, ∑ k ∈ Icc 1 m,
          ∫⁻ ω, (if bhK α (Y i ω) = k ∧ p i ω ≤ α * k / m then ((k : ℝ≥0∞))⁻¹ else 0) ∂P := by
        rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun k _ => hFmeas i k]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ fun k _ => hFmeas i k]
    _ ≤ ∑ i ∈ H₀, ∑ k ∈ Icc 1 m, ENNReal.ofReal (α / m) * P (A i k) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk => hterm i hi k hk
    _ = ∑ i ∈ H₀, ENNReal.ofReal (α / m) * ∑ k ∈ Icc 1 m, P (A i k) := by
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ H₀, ENNReal.ofReal (α / m) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ENNReal.ofReal (α / m) * ∑ k ∈ Icc 1 m, P (A i k)
            ≤ ENNReal.ofReal (α / m) * 1 := by gcongr; exact hsumA i
          _ = ENNReal.ofReal (α / m) := mul_one _
    _ = ENNReal.ofReal (α * H₀.card / m) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast H₀.card,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1; ring

/-- Mutually independent p-values satisfy the leave-one-out independence used by
`fdr_bhReject_le`. -/
lemma indepFun_update_of_iIndepFun (P : Measure Ω) (p : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (i : ι) :
    IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P := by
  have hdisj : Disjoint ({i} : Finset ι) (univ.erase i) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    exact (Finset.mem_erase.mp hj').1 (Finset.mem_singleton.mp hj)
  have h := hindep.indepFun_finset {i} (univ.erase i) hdisj hmeas
  set φ : (({i} : Finset ι) → ℝ) → ℝ := fun y => y ⟨i, Finset.mem_singleton_self i⟩ with hφ
  set ψ : ({j // j ∈ univ.erase i} → ℝ) → ι → ℝ :=
    fun y j => if hj : j = i then 0 else y ⟨j, Finset.mem_erase.mpr ⟨hj, mem_univ j⟩⟩ with hψ
  have hφm : Measurable φ := measurable_pi_apply _
  have hψm : Measurable ψ := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : j = i
    · have : (fun y => ψ y j) = fun _ => 0 := by funext y; simp [hψ, hj]
      rw [this]; exact measurable_const
    · have : (fun y => ψ y j) = fun y => y ⟨j, Finset.mem_erase.mpr ⟨hj, mem_univ j⟩⟩ := by
        funext y; simp [hψ, hj]
      rw [this]; exact measurable_pi_apply _
  have h' := h.comp hφm hψm
  have e2 : (ψ ∘ fun ω (j : {j // j ∈ univ.erase i}) => p j ω)
      = fun ω => Function.update (fun j => p j ω) i 0 := by
    funext ω j
    by_cases hji : j = i
    · subst hji; simp [hψ]
    · simp [hψ, hji]
  rw [e2] at h'
  exact h'

/-- **Benjamini–Hochberg theorem**, textbook form: for mutually independent p-values that are
valid under their nulls, the procedure at level `α` has false discovery rate at most `α`. -/
theorem fdr_bhReject_le_of_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω) ≤ ENNReal.ofReal α := by
  refine (fdr_bhReject_le P hα p hmeas H₀ hvalid fun i _ =>
    indepFun_update_of_iIndepFun P p hmeas hindep i).trans (ENNReal.ofReal_le_ofReal ?_)
  have hcard : (H₀.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast H₀.card_le_univ
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · simp [h0, hα]
  · have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hpos
    rw [div_le_iff₀ hm]
    nlinarith

end Probabilistic

end Applied.MultipleTesting
