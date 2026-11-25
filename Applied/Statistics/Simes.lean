import Applied.Statistics.BenjaminiHochberg
import Applied.Statistics.ClosedTesting

/-!
# Simes inequality, Hommel and Hochberg procedures

* `measure_one_le_bhK_le`: the **Simes inequality**. For independent valid p-values, the chance
  that `p₍ₖ₎ ≤ α k / m` for some `k` is at most `α`. It is the Benjamini–Hochberg theorem with
  every hypothesis a true null.
* `hommel`: the closed test built from Simes local tests; `fwer_hommel_le`.
* `hochberg`: Hochberg's step-up procedure, with the textbook treatment of tied p-values (a
  block of ties uses the divisor of its last position); `hochberg_subset_hommel`,
  `fwer_hochberg_le`. `hochberg_firstPosition_subset`: it rejects at least what the more
  conservative first-position rule rejects.
* `fwer_hommel_le_of_null_iIndepFun`, `fwer_hochberg_le_of_null_iIndepFun`,
  `measure_simesLocal_le_of_null_iIndepFun`: the same bounds assuming independence only among
  the p-values of the true nulls (the hypothesis used in the literature). `fwer_hommel_le` and
  `fwer_hochberg_le` assume that all p-values are independent, which is more than needed. In
  `measure_one_le_bhK_le` every hypothesis is a true null, so there the two hypotheses agree.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [MeasurableSpace Ω]

section Simes

variable [Fintype ι] [DecidableEq ι] {α : ℝ}

omit [MeasurableSpace Ω] [DecidableEq ι] in
lemma bhReject_nonempty_of_one_le_bhK (q : ι → ℝ) (h : 1 ≤ bhK α q) :
    (bhReject α q).Nonempty :=
  Finset.card_pos.mp (lt_of_lt_of_le h (bhK_le_card_bhReject q))

/-- The Simes test rejects with probability at most the false discovery rate of
Benjamini–Hochberg when every hypothesis is a true null. -/
theorem measure_one_le_bhK_le_fdr (P : Measure Ω) (p : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (p i)) :
    P {ω | 1 ≤ bhK α fun j => p j ω} ≤ fdr P univ (fun ω => bhReject α fun j => p j ω) := by
  have hpm : Measurable fun ω => (fun j => p j ω) := measurable_pi_iff.mpr hmeas
  have hS : MeasurableSet {ω | 1 ≤ bhK α fun j => p j ω} := by
    have h := (measurable_bhK (α := α)).comp hpm
    have hset : {ω | 1 ≤ bhK α fun j => p j ω}
        = (fun ω => bhK α fun j => p j ω) ⁻¹' {0}ᶜ := by
      ext ω; simp [Nat.one_le_iff_ne_zero]
    rw [hset]; exact h (measurableSet_singleton 0).compl
  have hpt : ∀ ω, ({ω | 1 ≤ bhK α fun j => p j ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω)
      ≤ fdp univ (bhReject α fun j => p j ω) := by
    intro ω
    by_cases h : 1 ≤ bhK α fun j => p j ω
    · have hne := bhReject_nonempty_of_one_le_bhK _ h
      have hcard : ((bhReject α fun j => p j ω).card : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr hne).ne'
      rw [Set.indicator_of_mem (by exact h), fdp, Finset.inter_univ,
        ENNReal.div_self hcard (ENNReal.natCast_ne_top _)]
    · rw [Set.indicator_of_notMem (by exact h)]; exact zero_le
  calc P {ω | 1 ≤ bhK α fun j => p j ω}
      = ∫⁻ ω, {ω | 1 ≤ bhK α fun j => p j ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
        rw [lintegral_indicator_const hS, one_mul]
    _ ≤ fdr P univ (fun ω => bhReject α fun j => p j ω) := lintegral_mono hpt

/-- **Simes inequality.** If all hypotheses are true nulls with independent valid p-values,
the Simes test rejects with probability at most `α`. The Simes test rejects when
`1 ≤ bhK α q`, i.e. when at least `k` of the p-values are at most `α k / m` for some `k ≥ 1`. -/
theorem measure_one_le_bhK_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P)
    (hvalid : ∀ i, IsValidPValue P (p i)) :
    P {ω | 1 ≤ bhK α fun j => p j ω} ≤ ENNReal.ofReal α :=
  (measure_one_le_bhK_le_fdr P p hmeas).trans
    (fdr_bhReject_le_of_iIndepFun P hα p hmeas hindep univ fun i _ => hvalid i)

/-- The Simes local test of the intersection hypothesis `I`. -/
def simesLocal (α : ℝ) (p : ι → Ω → ℝ) (I : Finset ι) (ω : Ω) : Prop :=
  1 ≤ bhK α fun j : I => p j ω

omit [Fintype ι] in
/-- The Simes test of the true intersection hypothesis has level `α`. -/
theorem measure_simesLocal_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    P {ω | simesLocal α p H₀ ω} ≤ ENNReal.ofReal α :=
  measure_one_le_bhK_le P hα (fun j : H₀ => p j) (fun j => hmeas j)
    (hindep.precomp Subtype.val_injective) fun j => hvalid j j.2

/-- Hommel's procedure: the closed test built from Simes local tests. -/
noncomputable def hommel (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  closedTest (simesLocal α p) ω

/-- **Hommel's procedure** controls the family-wise error rate for independent p-values. -/
theorem fwer_hommel_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fwer P H₀ (hommel α p) ≤ ENNReal.ofReal α :=
  fwer_closedTest_le P _ H₀ _ (measure_simesLocal_le P hα p hmeas hindep H₀ hvalid)

open Classical in
/-- Hochberg's step-up procedure: reject `i` when some `j` with `p i ≤ p j` satisfies
`p j ≤ α / (#{l | p j < p l} + 1)`.

This is the textbook rule (sort `p₍₁₎ ≤ … ≤ p₍ₘ₎`, take the largest `k` with
`p₍ₖ₎ ≤ α / (m - k + 1)`, reject the hypotheses at positions `1, …, k`), written without
sorting. Without ties `#{l | p j < p l} + 1 = m - rank j + 1`. With ties, the p-values equal
to `p j` occupy a block of consecutive positions and `#{l | p j < p l} + 1` is the divisor
`m - k + 1` of the *last* position `k` of that block, the most favourable one in the block
when `α ≥ 0`. Hence for `α ≥ 0` every way of ordering tied p-values gives this same rejection
set: if the textbook rule stops at position `k`, the last position of the block of `p₍ₖ₎`
also passes, and everything at or below that block is rejected. (The equivalence with the
sorted formulation, for `α ≥ 0`, `ι = Fin m` and every sorting permutation, is
`hochbergSorted_eq_hochberg` in `Applied.Statistics.SortedProcedures`; for `α < 0` the sorted
rule can depend on the order of ties and no claim is made.)

`hochberg_firstPosition_subset` compares this with the more conservative rule that divides by
`#{l | p j ≤ p l}` (the first position of the tie block), and `hochberg_eq_univ_of_forall_eq`
shows that equal p-values `x ≤ α` are all rejected. -/
noncomputable def hochberg (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | ∃ j, p i ω ≤ p j ω ∧
    p j ω ≤ α / (((univ.filter fun l => p j ω < p l ω).card : ℝ) + 1)}

omit [MeasurableSpace Ω] [DecidableEq ι] in
lemma mem_hochberg {p : ι → Ω → ℝ} {ω : Ω} {i : ι} :
    i ∈ hochberg α p ω ↔ ∃ j, p i ω ≤ p j ω ∧
      p j ω ≤ α / (((univ.filter fun l => p j ω < p l ω).card : ℝ) + 1) := by
  classical
  simp [hochberg]

omit [MeasurableSpace Ω] [DecidableEq ι] in
open Classical in
/-- The corrected rule rejects everything rejected by the more conservative rule that divides
by `#{l | p j ≤ p l}`, the divisor of the *first* position of a block of tied p-values. -/
theorem hochberg_firstPosition_subset (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    (univ.filter fun i => ∃ j, p i ω ≤ p j ω ∧
        p j ω ≤ α / (univ.filter fun l => p j ω ≤ p l ω).card) ⊆ hochberg α p ω := by
  intro i hi
  obtain ⟨j, hij, hj⟩ := (mem_filter.mp hi).2
  refine mem_hochberg.mpr ⟨j, hij, hj.trans ?_⟩
  have hlt : (univ.filter fun l => p j ω < p l ω).card
      < (univ.filter fun l => p j ω ≤ p l ω).card := by
    refine Finset.card_lt_card ⟨fun l hl => ?_, fun hsub => ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hl ⊢
      exact hl.le
    · have : j ∈ univ.filter fun l : ι => p j ω < p l ω := hsub (by simp)
      simp at this
  have hle : ((univ.filter fun l => p j ω < p l ω).card : ℝ) + 1
      ≤ (univ.filter fun l => p j ω ≤ p l ω).card := by
    exact_mod_cast hlt
  exact div_le_div_of_nonneg_left hα (by positivity) hle

omit [MeasurableSpace Ω] [DecidableEq ι] in
/-- If all p-values are equal to `x ≤ α`, Hochberg's procedure rejects every hypothesis. -/
theorem hochberg_eq_univ_of_forall_eq {p : ι → Ω → ℝ} {ω : Ω} {x : ℝ}
    (hp : ∀ i, p i ω = x) (hx : x ≤ α) : hochberg α p ω = univ := by
  refine Finset.eq_univ_iff_forall.mpr fun i => mem_hochberg.mpr ⟨i, le_rfl, ?_⟩
  have h0 : (univ.filter fun l => p i ω < p l ω) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun l _ => by simp [hp]
  rw [h0, hp i]
  simpa using hx

omit [MeasurableSpace Ω] [DecidableEq ι] in
open Classical in
/-- If all p-values are equal to `x > α / m`, the more conservative rule that divides by
`#{l | p j ≤ p l}` rejects nothing. With `hochberg_eq_univ_of_forall_eq`: for `m = 2` and
`p₁ = p₂ = x` with `α / 2 < x ≤ α`, Hochberg's procedure rejects both hypotheses and the
conservative rule rejects none. -/
theorem firstPosition_eq_empty_of_forall_eq {p : ι → Ω → ℝ} {ω : Ω} {x : ℝ}
    (hp : ∀ i, p i ω = x) (hx : α / Fintype.card ι < x) :
    (univ.filter fun i => ∃ j, p i ω ≤ p j ω ∧
        p j ω ≤ α / (univ.filter fun l => p j ω ≤ p l ω).card) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun i _ => ?_
  rintro ⟨j, -, hj⟩
  have h1 : (univ.filter fun l => p j ω ≤ p l ω) = univ :=
    Finset.filter_eq_self.mpr fun l _ => by simp [hp]
  rw [h1, Finset.card_univ, hp j] at hj
  exact not_lt.mpr hj hx

/-- Two tied p-values `α / 2 < x ≤ α`: Hochberg's procedure rejects both. -/
example (p : Fin 2 → Ω → ℝ) (ω : Ω) (x : ℝ) (hp : ∀ i, p i ω = x) (hx : x ≤ α) :
    hochberg α p ω = univ :=
  hochberg_eq_univ_of_forall_eq hp hx

omit [MeasurableSpace Ω] in
/-- Everything Hochberg rejects, Hommel rejects. -/
theorem hochberg_subset_hommel (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    hochberg α p ω ⊆ hommel α p ω := by
  classical
  intro i hi
  obtain ⟨j, hij, hj⟩ := mem_hochberg.mp hi
  simp only [hommel, closedTest, mem_filter, mem_univ, true_and]
  intro I hiI
  -- `a` counts the members of `I` whose p-value is at most `p j`
  set F := univ.filter fun l : I => p l ω ≤ p j ω with hF
  set a := F.card with ha
  have ha1 : 1 ≤ a := Finset.card_pos.mpr ⟨⟨i, hiI⟩, by simp [hF, hij]⟩
  have han : a ≤ Fintype.card I := by
    rw [ha, ← Finset.card_univ]; exact Finset.card_le_card (Finset.filter_subset _ _)
  set N := (univ.filter fun l => p j ω < p l ω).card + 1 with hN
  -- members of `I` with a strictly larger p-value inject into `{l | p j < p l}`
  have hrest : Fintype.card I - a + 1 ≤ N := by
    have h1 : (univ.filter fun l : I => ¬ p l ω ≤ p j ω).card = Fintype.card I - a := by
      have h0 : a + (univ.filter fun l : I => ¬ p l ω ≤ p j ω).card = Fintype.card I := by
        rw [ha, hF, ← Finset.card_univ]
        exact Finset.card_filter_add_card_filter_not _
      omega
    have h2 : (univ.filter fun l : I => ¬ p l ω ≤ p j ω).card
        ≤ (univ.filter fun l : ι => p j ω < p l ω).card := by
      refine Finset.card_le_card_of_injOn (fun l => (l : ι)) ?_ ?_
      · intro l hl
        have := (mem_filter.mp (mem_coe.mp hl)).2
        exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, not_le.mp this⟩)
      · exact fun x _ y _ hxy => Subtype.ext hxy
    omega
  have hj' : p j ω ≤ α / (N : ℝ) := by
    rw [hN]; push_cast; exact hj
  -- hence `p j ≤ α a / |I|`
  have hnpos : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast lt_of_lt_of_le ha1 han
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hthr : p j ω ≤ α * a / Fintype.card I := by
    refine hj'.trans ?_
    rw [div_le_div_iff₀ hNpos hnpos]
    have hreal : (Fintype.card I : ℝ) - a + 1 ≤ N := by
      have : ((Fintype.card I - a + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hrest
      rw [Nat.cast_add, Nat.cast_sub han] at this
      simpa using this
    have ha1r : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hanr : (a : ℝ) ≤ Fintype.card I := by exact_mod_cast han
    have key : (Fintype.card I : ℝ) ≤ a * N := by nlinarith
    nlinarith
  refine ha1.trans (le_bhK _ han ?_)
  refine Finset.card_le_card fun l hl => ?_
  simp only [hF, mem_filter, mem_univ, true_and] at hl ⊢
  exact hl.trans hthr

/-- **Hochberg's procedure** controls the family-wise error rate for independent p-values. -/
theorem fwer_hochberg_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fwer P H₀ (hochberg α p) ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans (fwer_hommel_le P hα p hmeas hindep H₀ hvalid)
  rintro ω ⟨i, hi, hrej⟩
  exact ⟨i, hi, hochberg_subset_hommel hα p ω hrej⟩

/-! ### Independence among the true nulls only

The theorems above assume that *all* p-values are mutually independent. The literature needs
independence only among the p-values of the true nulls; the p-values of the false nulls may
be arbitrary (any joint law, any dependence on the null p-values). The versions below take
`iIndepFun (fun j : H₀ => p j) P` and imply the versions above. -/

omit [Fintype ι] in
/-- The Simes test of the true intersection hypothesis has level `α`, when the p-values of the
true nulls are mutually independent. Nothing is assumed about the other p-values. -/
theorem measure_simesLocal_le_of_null_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P]
    (hα : 0 ≤ α) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hindep : iIndepFun (fun j : H₀ => p j) P) (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    P {ω | simesLocal α p H₀ ω} ≤ ENNReal.ofReal α :=
  measure_one_le_bhK_le P hα (fun j : H₀ => p j) (fun j => hmeas j) hindep fun j => hvalid j j.2

/-- **Hommel's procedure** controls the family-wise error rate when the p-values of the true
nulls are mutually independent. Nothing is assumed about the dependence of the other p-values.
`fwer_hommel_le` is the special case in which all p-values are independent. -/
theorem fwer_hommel_le_of_null_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hindep : iIndepFun (fun j : H₀ => p j) P) (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fwer P H₀ (hommel α p) ≤ ENNReal.ofReal α :=
  fwer_closedTest_le P _ H₀ _
    (measure_simesLocal_le_of_null_iIndepFun P hα p hmeas H₀ hindep hvalid)

/-- **Hochberg's procedure** controls the family-wise error rate when the p-values of the true
nulls are mutually independent. Nothing is assumed about the dependence of the other p-values.
`fwer_hochberg_le` is the special case in which all p-values are independent. -/
theorem fwer_hochberg_le_of_null_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P]
    (hα : 0 ≤ α) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hindep : iIndepFun (fun j : H₀ => p j) P) (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fwer P H₀ (hochberg α p) ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans
    (fwer_hommel_le_of_null_iIndepFun P hα p hmeas H₀ hindep hvalid)
  rintro ω ⟨i, hi, hrej⟩
  exact ⟨i, hi, hochberg_subset_hommel hα p ω hrej⟩

end Simes

end Applied.MultipleTesting
