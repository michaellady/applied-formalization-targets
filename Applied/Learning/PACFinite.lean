import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# PAC bound for a finite hypothesis class (realizable case)

The sample is a family `Z : Fin n → Ω → 𝒵` of independent random examples on a probability
space `(Ω, μ)`, each with law `P` (`μ.map (Z i) = P`). A hypothesis `h` is represented only
through its error region `E h : Set 𝒵`, the set of examples on which it errs; its true error
is `P (E h)` and it has zero empirical error on the sample when no `Z i ω` lies in `E h`.

* `measureReal_forall_notMem`: for one measurable region `A`,
  `P(∀ i, Z i ∉ A) = (1 - P A) ^ n`.
* `pac_finite_realizable`: `P(∃ h ∈ H, P (E h) > ε ∧ h has zero empirical error)
  ≤ |H| (1 - ε) ^ n`.
* `pac_finite_realizable_exp`: the same probability is at most `|H| exp (-ε n)`.
* `pac_finite_realizable_sample_complexity`: it is at most `δ` once `n ≥ log (|H| / δ) / ε`.
* `pac_finite_realizable_pi`: the bound on the product space `(𝒵ⁿ, Pⁿ)` with coordinate maps.
-/

open MeasureTheory ProbabilityTheory Finset

namespace Applied.Learning

variable {Ω 𝒵 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒵]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure 𝒵} {n : ℕ} {Z : Fin n → Ω → 𝒵}

/-- The probability that none of `n` i.i.d. examples falls in a region `A` is
`(1 - P A) ^ n`. -/
theorem measureReal_forall_notMem (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = P) {A : Set 𝒵} (hA : MeasurableSet A) :
    μ.real {ω | ∀ i, Z i ω ∉ A} = (1 - P.real A) ^ n := by
  have hset : {ω | ∀ i, Z i ω ∉ A} = ⋂ i ∈ (univ : Finset (Fin n)), Z i ⁻¹' Aᶜ := by
    ext ω; simp
  have hprod : μ (⋂ i ∈ (univ : Finset (Fin n)), Z i ⁻¹' Aᶜ)
      = ∏ i ∈ (univ : Finset (Fin n)), μ (Z i ⁻¹' Aᶜ) :=
    hind.meas_biInter (fun i _ => ⟨Aᶜ, hA.compl, rfl⟩)
  have hone : ∀ i, μ.real (Z i ⁻¹' Aᶜ) = 1 - P.real A := by
    intro i
    have h1 : μ.real (Z i ⁻¹' Aᶜ) = 1 - μ.real (Z i ⁻¹' A) := by
      rw [Set.preimage_compl, probReal_compl_eq_one_sub (hZ i hA)]
    have h2 : μ.real (Z i ⁻¹' A) = P.real A := by
      rw [measureReal_def, measureReal_def, ← hlaw i, Measure.map_apply (hZ i) hA]
    rw [h1, h2]
  rw [hset, measureReal_def, hprod, ENNReal.toReal_prod]
  simp only [← measureReal_def, hone, prod_const, card_univ, Fintype.card_fin]

/-- **PAC bound, finite class, realizable case.** The probability that some hypothesis of the
finite class `H` has true error above `ε` and yet makes no error on `n` i.i.d. examples is at
most `|H| (1 - ε) ^ n`. -/
theorem pac_finite_realizable (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = P) (H : Finset ι) (E : ι → Set 𝒵)
    (hE : ∀ h ∈ H, MeasurableSet (E h)) {ε : ℝ} (hε : ε ≤ 1) :
    μ.real {ω | ∃ h ∈ H, ε < P.real (E h) ∧ ∀ i, Z i ω ∉ E h} ≤ H.card * (1 - ε) ^ n := by
  classical
  have hsub : {ω | ∃ h ∈ H, ε < P.real (E h) ∧ ∀ i, Z i ω ∉ E h}
      ⊆ ⋃ h ∈ H.filter (fun h => ε < P.real (E h)), {ω | ∀ i, Z i ω ∉ E h} := by
    rintro ω ⟨h, hH, hbad, hω⟩
    simp only [Set.mem_iUnion, mem_filter, Set.mem_ofPred_eq, exists_prop]
    exact ⟨h, ⟨hH, hbad⟩, hω⟩
  calc μ.real {ω | ∃ h ∈ H, ε < P.real (E h) ∧ ∀ i, Z i ω ∉ E h}
      ≤ μ.real (⋃ h ∈ H.filter (fun h => ε < P.real (E h)), {ω | ∀ i, Z i ω ∉ E h}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ h ∈ H.filter (fun h => ε < P.real (E h)), μ.real {ω | ∀ i, Z i ω ∉ E h} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ H.filter (fun h => ε < P.real (E h)), (1 - ε) ^ n := by
        refine sum_le_sum fun h hh => ?_
        rw [mem_filter] at hh
        rw [measureReal_forall_notMem hZ hind hlaw (hE h hh.1)]
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · have : IsProbabilityMeasure P := by
            rw [← hlaw ⟨0, hn⟩]
            exact (Measure.isProbabilityMeasure_map_iff (hZ _).aemeasurable).mpr inferInstance
          have h1 : P.real (E h) ≤ 1 := measureReal_le_one
          exact pow_le_pow_left₀ (by linarith) (by linarith) n
    _ = (H.filter (fun h => ε < P.real (E h))).card * (1 - ε) ^ n := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ H.card * (1 - ε) ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by linarith) n)
        exact_mod_cast card_le_card (filter_subset _ _)

/-- **PAC bound, exponential form.** The probability that some hypothesis with true error above
`ε` is consistent with `n` i.i.d. examples is at most `|H| exp (-ε n)`. -/
theorem pac_finite_realizable_exp (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = P) (H : Finset ι) (E : ι → Set 𝒵)
    (hE : ∀ h ∈ H, MeasurableSet (E h)) {ε : ℝ} (hε : ε ≤ 1) :
    μ.real {ω | ∃ h ∈ H, ε < P.real (E h) ∧ ∀ i, Z i ω ∉ E h}
      ≤ H.card * Real.exp (-ε * n) := by
  refine (pac_finite_realizable hZ hind hlaw H E hE hε).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc (1 - ε) ^ n ≤ Real.exp (-ε) ^ n :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-ε)]) n
    _ = Real.exp (-ε * n) := by rw [← Real.exp_nat_mul]; ring_nf

/-- **Sample complexity.** If `n ≥ log (|H| / δ) / ε`, then with probability at least `1 - δ`
every hypothesis consistent with the sample has true error at most `ε`: the failure
probability is at most `δ`. -/
theorem pac_finite_realizable_sample_complexity (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hlaw : ∀ i, μ.map (Z i) = P) (H : Finset ι) (E : ι → Set 𝒵)
    (hE : ∀ h ∈ H, MeasurableSet (E h)) {ε δ : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1) (hδ : 0 < δ)
    (hn : Real.log (H.card / δ) / ε ≤ n) :
    μ.real {ω | ∃ h ∈ H, ε < P.real (E h) ∧ ∀ i, Z i ω ∉ E h} ≤ δ := by
  rcases H.eq_empty_or_nonempty with rfl | hne
  · simpa using hδ.le
  refine (pac_finite_realizable_exp hZ hind hlaw H E hE hε).trans ?_
  have hc : (0 : ℝ) < H.card := by exact_mod_cast hne.card_pos
  have h1 : Real.log (H.card / δ) ≤ ε * n := by
    rw [div_le_iff₀ hε₀] at hn; linarith
  have h2 : Real.exp (-ε * n) ≤ δ / H.card := by
    rw [← Real.exp_log (div_pos hδ hc)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hδ.ne' hc.ne']
    rw [Real.log_div hc.ne' hδ.ne'] at h1
    linarith
  calc (H.card : ℝ) * Real.exp (-ε * n) ≤ H.card * (δ / H.card) :=
        mul_le_mul_of_nonneg_left h2 hc.le
    _ = δ := by field_simp

/-- **PAC bound on the product space.** The same bound for the sample space `𝒵ⁿ` with the
product measure `Pⁿ` and the coordinate maps as examples; this is the usual textbook
formulation, and shows that the hypotheses of `pac_finite_realizable` can be met. -/
theorem pac_finite_realizable_pi (P : Measure 𝒵) [IsProbabilityMeasure P] (n : ℕ)
    (H : Finset ι) (E : ι → Set 𝒵) (hE : ∀ h ∈ H, MeasurableSet (E h)) {ε : ℝ} (hε : ε ≤ 1) :
    (Measure.pi fun _ : Fin n => P).real {s | ∃ h ∈ H, ε < P.real (E h) ∧ ∀ i, s i ∉ E h}
      ≤ H.card * (1 - ε) ^ n := by
  refine pac_finite_realizable (μ := Measure.pi fun _ : Fin n => P) (P := P)
    (Z := fun i s => s i) (fun i => measurable_pi_apply i) ?_ ?_ H E hE hε
  · exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  · intro i
    exact (measurePreserving_eval (μ := fun _ : Fin n => P) i).map_eq

end Applied.Learning
