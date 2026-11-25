import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# Uniform convergence for a finite hypothesis class (agnostic case)

The sample is a family `Z : Fin n → Ω → 𝒵` of independent random examples on a probability
space `(Ω, μ)`, each with law `P`. A hypothesis `h` enters only through its loss function
`ℓ h : 𝒵 → ℝ`, measurable with values in `[0, 1]`.

* `empRisk ℓ Z h ω`: the empirical risk `(1/n) ∑ i, ℓ h (Z i ω)`.
* `risk P ℓ h`: the true risk `∫ z, ℓ h z ∂P`.
* `hoeffding_empRisk_upper`, `hoeffding_empRisk_lower`, `hoeffding_empRisk_abs`: Hoeffding's
  inequality for one hypothesis, `P(|empirical - true| ≥ ε) ≤ 2 exp (-2 n ε²)`.
* `uniform_convergence_finite`: union bound over a finite class,
  `P(∃ h ∈ H, |empirical - true| ≥ ε) ≤ 2 |H| exp (-2 n ε²)`.
* `uniform_convergence_finite_pi`: the same bound on the product space `(𝒵ⁿ, Pⁿ)`.
* `erm_risk_lt`: deterministic step: if all empirical risks are within `ε` of the true risks,
  an empirical risk minimiser is within `2 ε` of every hypothesis of the class.
* `erm_excess_risk`: the probability that an empirical risk minimiser has true risk at least
  `2 ε` above some hypothesis of the class is at most `2 |H| exp (-2 n ε²)`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace Applied.Learning

variable {Ω 𝒵 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒵]

/-- Empirical risk of hypothesis `h` on the sample `Z · ω` (equal to `0` when `n = 0`). -/
noncomputable def empRisk {n : ℕ} (ℓ : ι → 𝒵 → ℝ) (Z : Fin n → Ω → 𝒵) (h : ι) (ω : Ω) : ℝ :=
  (∑ i, ℓ h (Z i ω)) / n

/-- True risk of hypothesis `h` under the example distribution `P`. -/
noncomputable def risk (P : Measure 𝒵) (ℓ : ι → 𝒵 → ℝ) (h : ι) : ℝ := ∫ z, ℓ h z ∂P

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure 𝒵} {n : ℕ} {Z : Fin n → Ω → 𝒵}
  {ℓ : ι → 𝒵 → ℝ}

/-- Hoeffding's inequality for a sum of `n` independent centred losses, in both directions. -/
private lemma hoeffding_aux (hn : 0 < n) (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = P) {h : ι} (hm : Measurable (ℓ h))
    (hb : ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ empRisk ℓ Z h ω - risk P ℓ h} ≤ Real.exp (-2 * n * ε ^ 2) ∧
    μ.real {ω | ε ≤ risk P ℓ h - empRisk ℓ Z h ω} ≤ Real.exp (-2 * n * ε ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set R := risk P ℓ h with hR
  have hmean : ∀ i, μ[fun ω => ℓ h (Z i ω)] = R := by
    intro i
    rw [hR, risk, ← hlaw i, integral_map (hZ i).aemeasurable hm.aestronglyMeasurable]
  have hindX : iIndepFun (fun i ω => ℓ h (Z i ω) - R) μ :=
    hind.comp (fun _ z => ℓ h z - R) (fun _ => hm.sub_const R)
  have hsub : ∀ i ∈ (univ : Finset (Fin n)),
      HasSubgaussianMGF (fun ω => ℓ h (Z i ω) - R) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro i _
    have := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun ω => ℓ h (Z i ω))
      (a := 0) (b := 1) (hm.comp (hZ i)).aemeasurable (ae_of_all _ fun ω => hb _)
    rwa [hmean i] at this
  have hindN : iIndepFun (fun i ω => -(ℓ h (Z i ω) - R)) μ :=
    hindX.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hsubN : ∀ i ∈ (univ : Finset (Fin n)),
      HasSubgaussianMGF (fun ω => -(ℓ h (Z i ω) - R)) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ :=
    fun i hi => (hsub i hi).neg
  have hexp : Real.exp (-(n * ε) ^ 2 /
      (2 * ((∑ _i ∈ (univ : Finset (Fin n)), (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ)))
      = Real.exp (-2 * n * ε ^ 2) := by
    congr 1
    simp only [sub_zero, nnNorm_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hsum : ∀ ω, ∑ i, (ℓ h (Z i ω) - R) = n * (empRisk ℓ Z h ω - R) := by
    intro ω
    rw [sum_sub_distrib, empRisk]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  constructor
  · have key := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindX hsub
      (mul_nonneg hn'.le hε)
    rw [hexp] at key
    refine le_trans (le_of_eq ?_) key
    congr 1; ext ω
    simp only [Set.mem_ofPred_eq]
    rw [hsum ω]
    exact ⟨fun h1 => mul_le_mul_of_nonneg_left h1 hn'.le, fun h1 => le_of_mul_le_mul_left h1 hn'⟩
  · have key := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindN hsubN
      (mul_nonneg hn'.le hε)
    rw [hexp] at key
    refine le_trans (le_of_eq ?_) key
    congr 1; ext ω
    simp only [Set.mem_ofPred_eq]
    rw [sum_neg_distrib, hsum ω, ← mul_neg, neg_sub]
    exact ⟨fun h1 => mul_le_mul_of_nonneg_left h1 hn'.le, fun h1 => le_of_mul_le_mul_left h1 hn'⟩

/-- **Hoeffding, upper tail.** For one hypothesis with losses in `[0, 1]`, the empirical risk
exceeds the true risk by `ε` with probability at most `exp (-2 n ε²)`. -/
theorem hoeffding_empRisk_upper (hn : 0 < n) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hlaw : ∀ i, μ.map (Z i) = P) {h : ι} (hm : Measurable (ℓ h))
    (hb : ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ empRisk ℓ Z h ω - risk P ℓ h} ≤ Real.exp (-2 * n * ε ^ 2) :=
  (hoeffding_aux hn hZ hind hlaw hm hb hε).1

/-- **Hoeffding, lower tail.** -/
theorem hoeffding_empRisk_lower (hn : 0 < n) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hlaw : ∀ i, μ.map (Z i) = P) {h : ι} (hm : Measurable (ℓ h))
    (hb : ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ risk P ℓ h - empRisk ℓ Z h ω} ≤ Real.exp (-2 * n * ε ^ 2) :=
  (hoeffding_aux hn hZ hind hlaw hm hb hε).2

/-- **Hoeffding, two-sided.** -/
theorem hoeffding_empRisk_abs (hn : 0 < n) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hlaw : ∀ i, μ.map (Z i) = P) {h : ι} (hm : Measurable (ℓ h))
    (hb : ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |empRisk ℓ Z h ω - risk P ℓ h|} ≤ 2 * Real.exp (-2 * n * ε ^ 2) := by
  have hsub : {ω | ε ≤ |empRisk ℓ Z h ω - risk P ℓ h|}
      ⊆ {ω | ε ≤ empRisk ℓ Z h ω - risk P ℓ h} ∪ {ω | ε ≤ risk P ℓ h - empRisk ℓ Z h ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_abs.mp hω with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by linarith)
  calc μ.real {ω | ε ≤ |empRisk ℓ Z h ω - risk P ℓ h|}
      ≤ μ.real ({ω | ε ≤ empRisk ℓ Z h ω - risk P ℓ h}
          ∪ {ω | ε ≤ risk P ℓ h - empRisk ℓ Z h ω}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-2 * n * ε ^ 2) := by
        linarith [hoeffding_empRisk_upper hn hZ hind hlaw hm hb hε,
          hoeffding_empRisk_lower hn hZ hind hlaw hm hb hε]

/-- **Uniform convergence for a finite class.** With losses in `[0, 1]` and `n ≥ 1` i.i.d.
examples, the probability that some hypothesis of the finite class `H` has empirical risk at
least `ε` away from its true risk is at most `2 |H| exp (-2 n ε²)`. -/
theorem uniform_convergence_finite (hn : 0 < n) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hlaw : ∀ i, μ.map (Z i) = P) (H : Finset ι)
    (hm : ∀ h ∈ H, Measurable (ℓ h)) (hb : ∀ h ∈ H, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ h ∈ H, ε ≤ |empRisk ℓ Z h ω - risk P ℓ h|}
      ≤ 2 * H.card * Real.exp (-2 * n * ε ^ 2) := by
  have hset : {ω | ∃ h ∈ H, ε ≤ |empRisk ℓ Z h ω - risk P ℓ h|}
      = ⋃ h ∈ H, {ω | ε ≤ |empRisk ℓ Z h ω - risk P ℓ h|} := by
    ext ω; simp
  rw [hset]
  calc μ.real (⋃ h ∈ H, {ω | ε ≤ |empRisk ℓ Z h ω - risk P ℓ h|})
      ≤ ∑ h ∈ H, μ.real {ω | ε ≤ |empRisk ℓ Z h ω - risk P ℓ h|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ H, 2 * Real.exp (-2 * n * ε ^ 2) :=
        sum_le_sum fun h hh => hoeffding_empRisk_abs hn hZ hind hlaw (hm h hh) (hb h hh) hε
    _ = 2 * H.card * Real.exp (-2 * n * ε ^ 2) := by
        rw [sum_const, nsmul_eq_mul]; ring

/-- **ERM, deterministic step.** If every hypothesis of `H` has empirical risk `L h` within
`ε` of its true risk `R h` and `ĥ ∈ H` minimises `L` over `H`, then `R ĥ < R h + 2 ε` for
every `h ∈ H`. -/
theorem erm_risk_lt {H : Finset ι} {L R : ι → ℝ} {ε : ℝ} (hunif : ∀ h ∈ H, |L h - R h| < ε)
    {hhat : ι} (hhat_mem : hhat ∈ H) (hmin : ∀ h ∈ H, L hhat ≤ L h) {h : ι} (hh : h ∈ H) :
    R hhat < R h + 2 * ε := by
  have h1 := abs_lt.mp (hunif hhat hhat_mem)
  have h2 := abs_lt.mp (hunif h hh)
  linarith [hmin h hh]

/-- **ERM excess risk.** Let `ĥ ω ∈ H` minimise the empirical risk over the finite class `H`
(no measurability of the selection `ĥ` is needed). The probability that its true risk is at
least `2 ε` above the true risk of some hypothesis of `H` is at most
`2 |H| exp (-2 n ε²)`. -/
theorem erm_excess_risk (hn : 0 < n) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hlaw : ∀ i, μ.map (Z i) = P) (H : Finset ι)
    (hm : ∀ h ∈ H, Measurable (ℓ h)) (hb : ∀ h ∈ H, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hhat : Ω → ι) (hhat_mem : ∀ ω, hhat ω ∈ H)
    (hmin : ∀ ω, ∀ h ∈ H, empRisk ℓ Z (hhat ω) ω ≤ empRisk ℓ Z h ω) :
    μ.real {ω | ∃ h ∈ H, risk P ℓ h + 2 * ε ≤ risk P ℓ (hhat ω)}
      ≤ 2 * H.card * Real.exp (-2 * n * ε ^ 2) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (uniform_convergence_finite hn hZ hind hlaw H hm hb hε)
  intro ω hω
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le] at hcon
  obtain ⟨h, hh, hle⟩ := hω
  have := erm_risk_lt (L := fun h => empRisk ℓ Z h ω) (R := risk P ℓ) hcon (hhat_mem ω)
    (hmin ω) hh
  linarith

/-- **Uniform convergence on the product space.** The same bound for the sample space `𝒵ⁿ`
with the product measure `Pⁿ` and the coordinate maps as examples; this shows that the
hypotheses of `uniform_convergence_finite` can be met. -/
theorem uniform_convergence_finite_pi (P : Measure 𝒵) [IsProbabilityMeasure P] {n : ℕ}
    (hn : 0 < n) (H : Finset ι) (hm : ∀ h ∈ H, Measurable (ℓ h))
    (hb : ∀ h ∈ H, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => P).real
        {s | ∃ h ∈ H, ε ≤ |(∑ i, ℓ h (s i)) / n - ∫ z, ℓ h z ∂P|}
      ≤ 2 * H.card * Real.exp (-2 * n * ε ^ 2) := by
  refine uniform_convergence_finite (μ := Measure.pi fun _ : Fin n => P) (P := P)
    (Z := fun i s => s i) hn (fun i => measurable_pi_apply i) ?_ ?_ H hm hb hε
  · exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  · intro i
    exact (measurePreserving_eval (μ := fun _ : Fin n => P) i).map_eq

end Applied.Learning
