import Applied.Statistics.BHBracket
import Applied.Statistics.NormalCDF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Benjamini–Hochberg in a one-factor Gaussian model: a finite-sample lower bound for the FDR

The model: a common factor `z` and independent noises `ε i`, all standard normal, and statistics
`X i = θ i + b i * z + s i * ε i`. The probability space is `ℝ × (ι → ℝ)` with the product of
standard normal laws. Two-sided p-values `2 (1 - Φ(|X i|))`.

Conditionally on `z` the indicators `1{p i ≤ t}` are independent, so by Chebyshev's inequality
the numbers of p-values below finitely many thresholds are close to their conditional means.
Together with the deterministic bracketing of `Applied.Statistics.BHBracket` this gives
`fdr_factor_ge`: a lower bound for the false discovery rate of Benjamini–Hochberg as a finite
sum over bins of the factor. This is a finite-sample form of the argument of E. Dobriban,
arXiv:2607.12208 (2026), Sections 3–6, with Chebyshev's inequality in place of the
Glivenko–Cantelli theorem and Fatou's lemma.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

open Applied.Statistics

local notation "γ" => gaussianReal 0 1
local notation "Φ" => cdf (gaussianReal 0 1)

/-- Two-sided p-value of a z-statistic. -/
noncomputable def twoSidedPValue (x : ℝ) : ℝ := 2 * (1 - Φ |x|)

lemma measurable_twoSidedPValue : Measurable twoSidedPValue :=
  measurable_const.mul (measurable_const.sub
    ((monotone_cdf (gaussianReal 0 1)).measurable.comp measurable_norm))

variable {ι : Type*} [Fintype ι]

/-- The law of the noise vector: independent standard normal coordinates. -/
noncomputable def noiseMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => γ

instance : IsProbabilityMeasure (noiseMeasure ι) := by
  unfold noiseMeasure; infer_instance

/-- The law of (factor, noise): independent standard normal coordinates. -/
noncomputable def factorMeasure (ι : Type*) [Fintype ι] : Measure (ℝ × (ι → ℝ)) :=
  (γ).prod (noiseMeasure ι)

instance : IsProbabilityMeasure (factorMeasure ι) := by
  unfold factorMeasure; infer_instance

open Classical in
/-- **Chebyshev for counts of independent events.** For measurable sets `A i ⊆ ℝ`, the number
of indices `i ∈ S` with `ε i ∈ A i` deviates from its mean `∑ i ∈ S, γ(A i)` by at least `a`
with probability at most `|ι| / a²` under independent standard normal `ε i`. -/
theorem noise_count_deviation (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (S : Finset ι)
    {a : ℝ} (ha : 0 < a) :
    noiseMeasure ι {ε | a ≤ |((S.filter fun i => ε i ∈ A i).card : ℝ)
        - ∑ i ∈ S, (γ).real (A i)|}
      ≤ ENNReal.ofReal (Fintype.card ι / a ^ 2) := by
  classical
  set X : ι → ℝ → ℝ := fun i => if i ∈ S then (A i).indicator (fun _ => (1 : ℝ)) else 0 with hX
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hX, hi, ite_true]; exact measurable_const.indicator (hA i)
    · simp only [hX, hi, ite_false]; exact measurable_const
  have hXbound : ∀ i e, ‖X i e‖ ≤ 1 := by
    intro i e
    by_cases hi : i ∈ S
    · simp only [hX, hi, ite_true, Set.indicator]
      split_ifs <;> simp
    · simp [hX, hi]
  have hX2 : ∀ i, MemLp (X i) 2 γ := fun i =>
    MemLp.of_bound (hXmeas i).aestronglyMeasurable 1 (ae_of_all _ (hXbound i))
  set Y : (ι → ℝ) → ℝ := ∑ i, fun ε => X i (ε i) with hY
  have hYcard : ∀ ε : ι → ℝ, Y ε = ((S.filter fun i => ε i ∈ A i).card : ℝ) := by
    intro ε
    simp only [hY, Finset.sum_apply]
    rw [Finset.card_filter]
    push_cast
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ S)]
    have h1 : ∑ i ∈ univ.filter (· ∈ S), X i (ε i) = ∑ i ∈ S, if ε i ∈ A i then (1 : ℝ) else 0 := by
      have : univ.filter (· ∈ S) = S := by ext i; simp
      rw [this]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hX, hi, ite_true, Set.indicator]
    have h2 : ∑ i ∈ univ.filter (fun i => ¬ i ∈ S), X i (ε i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have : i ∉ S := (mem_filter.mp hi).2
        simp [hX, this]
    rw [h1, h2, add_zero]
  have hcomp2 : ∀ i, MemLp (fun ε : ι → ℝ => X i (ε i)) 2 (noiseMeasure ι) := fun i =>
    (hX2 i).comp_measurePreserving (measurePreserving_eval _ i)
  have hY2 : MemLp Y 2 (noiseMeasure ι) := by
    rw [hY]; exact memLp_finsetSum' _ fun i _ => hcomp2 i
  have hint : ∀ i, ∫ ε, X i (ε i) ∂(noiseMeasure ι) = ∫ e, X i e ∂γ := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) (noiseMeasure ι) γ :=
      measurePreserving_eval _ i
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (hXmeas i).aestronglyMeasurable]
  have hEY : ∫ ε, Y ε ∂(noiseMeasure ι) = ∑ i ∈ S, (γ).real (A i) := by
    have h1 : ∫ ε, Y ε ∂(noiseMeasure ι) = ∑ i, ∫ ε, X i (ε i) ∂(noiseMeasure ι) := by
      simp only [hY, Finset.sum_apply]
      exact integral_finsetSum _ fun i _ => (hcomp2 i).integrable (by norm_num)
    rw [h1]
    simp_rw [hint]
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ S)]
    have e1 : ∑ i ∈ univ.filter (· ∈ S), ∫ e, X i e ∂γ = ∑ i ∈ S, (γ).real (A i) := by
      have : univ.filter (· ∈ S) = S := by ext i; simp
      rw [this]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hX, hi, ite_true]
      exact integral_indicator_one (hA i)
    have e2 : ∑ i ∈ univ.filter (fun i => ¬ i ∈ S), ∫ e, X i e ∂γ = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have : i ∉ S := (mem_filter.mp hi).2
        simp [hX, this]
    rw [e1, e2, add_zero]
  have hvar : variance Y (noiseMeasure ι) ≤ Fintype.card ι := by
    have h1 : variance Y (noiseMeasure ι) = ∑ i, variance (X i) γ := by
      rw [hY]; exact variance_sum_pi hX2
    rw [h1]
    calc ∑ i, variance (X i) γ ≤ ∑ _i : ι, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (variance_le_expectation_sq (hXmeas i).aestronglyMeasurable).trans ?_
          have hle : ∀ e, (X i ^ 2) e ≤ 1 := by
            intro e
            have := hXbound i e
            rw [Real.norm_eq_abs] at this
            simp only [Pi.pow_apply]
            rw [← sq_abs]
            nlinarith [abs_nonneg (X i e)]
          calc ∫ e, (X i ^ 2) e ∂γ ≤ ∫ _e, (1 : ℝ) ∂γ :=
                integral_mono ((hX2 i).integrable_sq) (integrable_const _) hle
            _ = 1 := by simp
      _ = Fintype.card ι := by simp
  have hcheb := meas_ge_le_variance_div_sq hY2 ha
  have hset : {ε : ι → ℝ | a ≤ |((S.filter fun i => ε i ∈ A i).card : ℝ)
      - ∑ i ∈ S, (γ).real (A i)|} = {ε | a ≤ |Y ε - ∫ ε, Y ε ∂(noiseMeasure ι)|} := by
    ext ε
    simp only [Set.mem_ofPred_eq]
    rw [hEY, hYcard ε]
  rw [hset]
  refine hcheb.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr

section Model

variable (θ b s : ι → ℝ)

/-- The statistics of the one-factor model on `ℝ × (ι → ℝ)`: `θ i + b i * z + s i * ε i`. -/
def factorStat (i : ι) (ω : ℝ × (ι → ℝ)) : ℝ := θ i + b i * ω.1 + s i * ω.2 i

/-- The vector of two-sided p-values of the one-factor model. -/
noncomputable def factorP (ω : ℝ × (ι → ℝ)) : ι → ℝ :=
  fun i => twoSidedPValue (factorStat θ b s i ω)

/-- The set of noise values for which the `i`-th p-value is at most `t`, given the factor `z`. -/
def condSet (i : ι) (z t : ℝ) : Set ℝ := {e | twoSidedPValue (θ i + b i * z + s i * e) ≤ t}

omit [Fintype ι] in
lemma measurableSet_condSet (i : ι) (z t : ℝ) : MeasurableSet (condSet θ b s i z t) :=
  measurableSet_le (measurable_twoSidedPValue.comp
    (measurable_const.add (measurable_const.mul measurable_id))) measurable_const

/-- The conditional probability, given the factor `z`, that the `i`-th p-value is at most `t`. -/
noncomputable def condProb (i : ι) (z t : ℝ) : ℝ := (γ).real (condSet θ b s i z t)

omit [Fintype ι] in
lemma measurable_factorStat (i : ι) : Measurable (factorStat θ b s i) :=
  (measurable_const.add (measurable_const.mul measurable_fst)).add
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))

omit [Fintype ι] in
lemma measurable_cntLE_factorP (S : Finset ι) (t : ℝ) :
    Measurable fun ω => (cntLE S (factorP θ b s ω) t : ℝ) := by
  have : (fun ω => (cntLE S (factorP θ b s ω) t : ℝ))
      = fun ω => ∑ i ∈ S, if factorP θ b s ω i ≤ t then (1 : ℝ) else 0 := by
    funext ω; rw [cntLE, Finset.card_filter]; push_cast; rfl
  rw [this]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite
    (measurableSet_le (measurable_twoSidedPValue.comp (measurable_factorStat θ b s i))
      measurable_const) measurable_const measurable_const

/-- The event on which the counts bracket the Benjamini–Hochberg threshold between `v` and
`w` (through the cells `(lo j, hi j]`) and at least `m f` true nulls have p-value at most
`v`. -/
def goodEvent (α : ℝ) (H₀ : Finset ι) {J : Type*} (lo hi : J → ℝ) (v f : ℝ) :
    Set (ℝ × (ι → ℝ)) :=
  {ω | (∀ j, (cntLE univ (factorP θ b s ω) (hi j) : ℝ) < Fintype.card ι * lo j / α) ∧
    (Fintype.card ι : ℝ) * v / α + 1 ≤ cntLE univ (factorP θ b s ω) v ∧
    (Fintype.card ι : ℝ) * f ≤ cntLE H₀ (factorP θ b s ω) v}

lemma measurableSet_goodEvent (α : ℝ) (H₀ : Finset ι) {J : Type*} [Finite J] (lo hi : J → ℝ)
    (v f : ℝ) : MeasurableSet (goodEvent θ b s α H₀ lo hi v f) := by
  have h1 : MeasurableSet {ω : ℝ × (ι → ℝ) | ∀ j, (cntLE univ (factorP θ b s ω) (hi j) : ℝ)
      < Fintype.card ι * lo j / α} := by
    have : {ω : ℝ × (ι → ℝ) | ∀ j, (cntLE univ (factorP θ b s ω) (hi j) : ℝ)
        < Fintype.card ι * lo j / α} = ⋂ j, {ω | (cntLE univ (factorP θ b s ω) (hi j) : ℝ)
        < Fintype.card ι * lo j / α} := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_lt (measurable_cntLE_factorP θ b s _ _) measurable_const
  exact h1.inter ((measurableSet_le measurable_const (measurable_cntLE_factorP θ b s _ _)).inter
    (measurableSet_le measurable_const (measurable_cntLE_factorP θ b s _ _)))

open Classical in
/-- Given the factor `z`, the good event fails with probability at most
`(|J| + 2) / (η² m)` as soon as the conditional means of the counts satisfy the three
inequalities with slack `η m`. -/
theorem noise_goodEvent_compl_le (α : ℝ) (H₀ : Finset ι) {J : Type*} [Fintype J]
    (lo hi : J → ℝ) (v f : ℝ) (z : ℝ) {η : ℝ} (hη : 0 < η) (hm : 0 < Fintype.card ι)
    (hU : ∀ j, ∑ i, condProb θ b s i z (hi j) + η * Fintype.card ι
      ≤ Fintype.card ι * lo j / α)
    (hL : (Fintype.card ι : ℝ) * v / α + 1 ≤ ∑ i, condProb θ b s i z v - η * Fintype.card ι)
    (hN : (Fintype.card ι : ℝ) * f ≤ ∑ i ∈ H₀, condProb θ b s i z v - η * Fintype.card ι) :
    noiseMeasure ι (Prod.mk z ⁻¹' (goodEvent θ b s α H₀ lo hi v f)ᶜ)
      ≤ (Fintype.card J + 2 : ℕ) * ENNReal.ofReal (1 / (η ^ 2 * Fintype.card ι)) := by
  set m := Fintype.card ι with hmdef
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 < η * m := mul_pos hη hmpos
  -- the deviation events
  set D : Finset ι → ℝ → Set (ι → ℝ) := fun S t =>
    {ε | η * m ≤ |((S.filter fun i => ε i ∈ condSet θ b s i z t).card : ℝ)
      - ∑ i ∈ S, (γ).real (condSet θ b s i z t)|} with hD
  have hDle : ∀ S t, noiseMeasure ι (D S t) ≤ ENNReal.ofReal (1 / (η ^ 2 * m)) := by
    intro S t
    refine (noise_count_deviation (fun i => condSet θ b s i z t)
      (fun i => measurableSet_condSet θ b s i z t) S ha).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (η * m) ^ 2 = η ^ 2 * m * m := by ring
    rw [this]
    nlinarith [mul_pos (pow_pos hη 2) hmpos]
  have hcnt : ∀ (S : Finset ι) (t : ℝ) (ε : ι → ℝ), cntLE S (factorP θ b s (z, ε)) t
      = (S.filter fun i => ε i ∈ condSet θ b s i z t).card := by
    intro S t ε
    rw [cntLE]
    congr 1
  have hsub : Prod.mk z ⁻¹' (goodEvent θ b s α H₀ lo hi v f)ᶜ
      ⊆ (⋃ j, D univ (hi j)) ∪ (D univ v ∪ D H₀ v) := by
    intro ε hε
    simp only [Set.mem_preimage, Set.mem_compl_iff, goodEvent, Set.mem_ofPred_eq, not_and_or,
      not_forall, not_lt, not_le] at hε
    rcases hε with ⟨j, hj⟩ | hε | hε
    · left
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      simp only [hD, Set.mem_ofPred_eq]
      rw [hcnt] at hj
      have hU' := hU j
      simp only [condProb] at hU'
      refine le_trans ?_ (le_abs_self _)
      linarith
    · right; left
      simp only [hD, Set.mem_ofPred_eq]
      rw [hcnt] at hε
      simp only [condProb] at hL
      refine le_trans ?_ (neg_le_abs _)
      linarith
    · right; right
      simp only [hD, Set.mem_ofPred_eq]
      rw [hcnt] at hε
      simp only [condProb] at hN
      refine le_trans ?_ (neg_le_abs _)
      linarith
  calc noiseMeasure ι (Prod.mk z ⁻¹' (goodEvent θ b s α H₀ lo hi v f)ᶜ)
      ≤ noiseMeasure ι ((⋃ j, D univ (hi j)) ∪ (D univ v ∪ D H₀ v)) := measure_mono hsub
    _ ≤ noiseMeasure ι (⋃ j, D univ (hi j)) + (noiseMeasure ι (D univ v)
          + noiseMeasure ι (D H₀ v)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ∑ j : J, noiseMeasure ι (D univ (hi j)) + (noiseMeasure ι (D univ v)
          + noiseMeasure ι (D H₀ v)) := by
        gcongr
        exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : J, ENNReal.ofReal (1 / (η ^ 2 * m)) + (ENNReal.ofReal (1 / (η ^ 2 * m))
          + ENNReal.ofReal (1 / (η ^ 2 * m))) := by
        gcongr with j
        · exact hDle _ _
        · exact hDle _ _
        · exact hDle _ _
    _ = (Fintype.card J + 2 : ℕ) * ENNReal.ofReal (1 / (η ^ 2 * m)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

end Model

/-- If the slices of a measurable event `G` at every factor value `z ∈ B` have probability at
least `1 - δ`, then `G ∩ (B × univ)` has probability at least `γ(B) (1 - δ)`. -/
lemma factorMeasure_inter_ge {G : Set (ℝ × (ι → ℝ))} (hG : MeasurableSet G) {B : Set ℝ}
    (hB : MeasurableSet B) (δ : ℝ≥0∞)
    (h : ∀ z ∈ B, noiseMeasure ι (Prod.mk z ⁻¹' Gᶜ) ≤ δ) :
    (γ) B * (1 - δ) ≤ factorMeasure ι (G ∩ (B ×ˢ Set.univ)) := by
  have hmeas : MeasurableSet (G ∩ (B ×ˢ (Set.univ : Set (ι → ℝ)))) :=
    hG.inter (hB.prod MeasurableSet.univ)
  rw [factorMeasure, Measure.prod_apply hmeas]
  calc (γ) B * (1 - δ) = ∫⁻ _z in B, (1 - δ) ∂γ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ z in B, noiseMeasure ι (Prod.mk z ⁻¹' (G ∩ (B ×ˢ Set.univ))) ∂γ := by
        refine setLIntegral_mono' hB fun z hz => ?_
        have hpre : Prod.mk z ⁻¹' (G ∩ (B ×ˢ (Set.univ : Set (ι → ℝ)))) = Prod.mk z ⁻¹' G := by
          ext ε; simp [hz]
        rw [hpre]
        have hGz : MeasurableSet (Prod.mk z ⁻¹' G) := measurable_prodMk_left hG
        have hcompl : noiseMeasure ι (Prod.mk z ⁻¹' G)ᶜ ≤ δ := h z hz
        rw [prob_compl_eq_one_sub hGz] at hcompl
        calc 1 - δ ≤ 1 - (1 - noiseMeasure ι (Prod.mk z ⁻¹' G)) := tsub_le_tsub_left hcompl 1
          _ = noiseMeasure ι (Prod.mk z ⁻¹' G) :=
            ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one
    _ ≤ ∫⁻ z, noiseMeasure ι (Prod.mk z ⁻¹' (G ∩ (B ×ˢ Set.univ))) ∂γ :=
        setLIntegral_le_lintegral _ _

variable [DecidableEq ι]

/-- **Finite-sample lower bound for the false discovery rate of Benjamini–Hochberg in a
one-factor Gaussian model.** The factor axis carries finitely many pairwise disjoint measurable
bins `B k`. For each bin there are thresholds `0 < v k ≤ α`, `0 < w k`, cells
`(lo k j, hi k j]` covering `(w k, α]`, and a number `f k ≥ 0`, such that for every factor
value `z ∈ B k` the conditional means of the counts satisfy, with slack `η m`:
the mean number of p-values at most `hi k j` is at most `m lo k j / α - η m`; the mean number
of p-values at most `v k` is at least `m v k / α + 1 + η m`; the mean number of true-null
p-values at most `v k` is at least `m f k + η m`. Then the false discovery rate is at least
`∑ k, (α f k / w k) γ(B k) (1 - (J k + 2) / (η² m))`. -/
theorem fdr_factor_ge (θ b s : ι → ℝ) {α : ℝ} (hα : 0 < α) (H₀ : Finset ι)
    {𝒦 : Type*} [Fintype 𝒦] (B : 𝒦 → Set ℝ) (hB : ∀ k, MeasurableSet (B k))
    (hdisj : Pairwise (Function.onFun Disjoint B)) {J : 𝒦 → Type*} [∀ k, Fintype (J k)]
    (lo hi : ∀ k, J k → ℝ) (v w f : 𝒦 → ℝ) {η : ℝ} (hη : 0 < η)
    (hv0 : ∀ k, 0 < v k) (hvα : ∀ k, v k ≤ α) (hw0 : ∀ k, 0 < w k) (hf : ∀ k, 0 ≤ f k)
    (hcover : ∀ k t, w k < t → t ≤ α → ∃ j, lo k j < t ∧ t ≤ hi k j)
    (hU : ∀ k, ∀ z ∈ B k, ∀ j, ∑ i, condProb θ b s i z (hi k j) + η * Fintype.card ι
      ≤ Fintype.card ι * lo k j / α)
    (hL : ∀ k, ∀ z ∈ B k, (Fintype.card ι : ℝ) * v k / α + 1
      ≤ ∑ i, condProb θ b s i z (v k) - η * Fintype.card ι)
    (hN : ∀ k, ∀ z ∈ B k, (Fintype.card ι : ℝ) * f k
      ≤ ∑ i ∈ H₀, condProb θ b s i z (v k) - η * Fintype.card ι) :
    ∑ k, ENNReal.ofReal (α * f k / w k) * ((γ) (B k) * (1 - (Fintype.card (J k) + 2 : ℕ)
        * ENNReal.ofReal (1 / (η ^ 2 * Fintype.card ι))))
      ≤ fdr (factorMeasure ι) H₀ (fun ω => bhReject α (factorP θ b s ω)) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hm0 | hm
  · -- no hypotheses: every bin is empty
    have hempty : ∀ k, B k = ∅ := by
      intro k
      by_contra hne
      obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have h1 := hL k z hz
      have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hm0
      simp at h1
      linarith
    calc ∑ k, ENNReal.ofReal (α * f k / w k) * ((γ) (B k) * (1 - (Fintype.card (J k) + 2 : ℕ)
          * ENNReal.ofReal (1 / (η ^ 2 * Fintype.card ι)))) = 0 :=
          Finset.sum_eq_zero fun k _ => by rw [hempty k]; simp
      _ ≤ _ := zero_le
  set G : 𝒦 → Set (ℝ × (ι → ℝ)) := fun k => goodEvent θ b s α H₀ (lo k) (hi k) (v k) (f k)
    with hGdef
  have hGmeas : ∀ k, MeasurableSet (G k) := fun k => measurableSet_goodEvent θ b s α H₀ _ _ _ _
  set E : 𝒦 → Set (ℝ × (ι → ℝ)) := fun k => G k ∩ (B k ×ˢ Set.univ) with hEdef
  have hEmeas : ∀ k, MeasurableSet (E k) := fun k =>
    (hGmeas k).inter ((hB k).prod MeasurableSet.univ)
  -- pointwise lower bound
  have hpt : ∀ ω, ∑ k, (E k).indicator (fun _ => ENNReal.ofReal (α * f k / w k)) ω
      ≤ fdp H₀ (bhReject α (factorP θ b s ω)) := by
    intro ω
    by_cases hex : ∃ k, ω ∈ E k
    · obtain ⟨k₀, hk₀⟩ := hex
      have hzero : ∀ k ∈ univ, k ≠ k₀ →
          (E k).indicator (fun _ => ENNReal.ofReal (α * f k / w k)) ω = 0 := by
        intro k _ hne
        refine Set.indicator_of_notMem (fun hk => ?_) _
        exact Set.disjoint_left.mp (hdisj hne) hk.2.1 hk₀.2.1
      rw [Finset.sum_eq_single_of_mem k₀ (mem_univ _) hzero, Set.indicator_of_mem hk₀]
      obtain ⟨hc1, hc2, hc3⟩ := hk₀.1
      exact fdp_bhReject_ge_of_bracket hα _ H₀ (hv0 k₀) (hvα k₀) (hw0 k₀) (hf k₀) (lo k₀)
        (hi k₀) (hcover k₀) hc1 hc2 hc3
    · have : ∀ k ∈ univ, (E k).indicator (fun _ => ENNReal.ofReal (α * f k / w k)) ω = 0 :=
        fun k _ => Set.indicator_of_notMem (fun hk => hex ⟨k, hk⟩) _
      rw [Finset.sum_eq_zero this]
      exact zero_le
  have hbin : ∀ k, (γ) (B k) * (1 - (Fintype.card (J k) + 2 : ℕ)
      * ENNReal.ofReal (1 / (η ^ 2 * Fintype.card ι))) ≤ factorMeasure ι (E k) := fun k =>
    factorMeasure_inter_ge (hGmeas k) (hB k) _ fun z hz =>
      noise_goodEvent_compl_le θ b s α H₀ (lo k) (hi k) (v k) (f k) z hη hm (hU k z hz)
        (hL k z hz) (hN k z hz)
  calc ∑ k, ENNReal.ofReal (α * f k / w k) * ((γ) (B k) * (1 - (Fintype.card (J k) + 2 : ℕ)
        * ENNReal.ofReal (1 / (η ^ 2 * Fintype.card ι))))
      ≤ ∑ k, ENNReal.ofReal (α * f k / w k) * factorMeasure ι (E k) :=
        Finset.sum_le_sum fun k _ => by gcongr; exact hbin k
    _ = ∑ k, ∫⁻ ω, (E k).indicator (fun _ => ENNReal.ofReal (α * f k / w k)) ω
          ∂(factorMeasure ι) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [lintegral_indicator_const (hEmeas k)]
    _ = ∫⁻ ω, ∑ k, (E k).indicator (fun _ => ENNReal.ofReal (α * f k / w k)) ω
          ∂(factorMeasure ι) := by
        rw [lintegral_finsetSum _ fun k _ => measurable_const.indicator (hEmeas k)]
    _ ≤ fdr (factorMeasure ι) H₀ (fun ω => bhReject α (factorP θ b s ω)) :=
        lintegral_mono hpt

end Applied.MultipleTesting
