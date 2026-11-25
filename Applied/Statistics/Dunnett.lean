import Applied.Statistics.PRDSFactorModels
import Applied.Statistics.ClosedTesting

/-!
# Dunnett's many-to-one procedure (known variance), single-step and step-down

## Generic part: closed max-statistic tests and their step-down shortcut

For statistics `T i` and critical values `c I` indexed by sets of hypotheses, the
max-statistic local test of the intersection hypothesis `I` rejects when `T i > c I` for some
`i ∈ I` (`maxLocal`). If the critical values are monotone on non-empty sets
(`MonotoneCrit`: `c J ≤ c I` for `∅ ≠ J ⊆ I`), the closed test equals

* the step-down rule written without sorting (`stepDownMax`,
  `closedTest_maxLocal_eq_stepDownMax`): `i` is rejected when every `j` with `T j ≥ T i` has
  `T j > c {l | T l ≤ T j}`;
* the outcome of any run of the sequential procedure that rejects one hypothesis `i` with
  `T i > c (not yet rejected)` at a time until none is left
  (`closedTest_maxLocal_eq_of_stepDownRejectable_of_maxStuck`,
  `exists_stepDownRejectable_maxStuck`).

## Dunnett's critical values

`dunnettCDF k d = ∫ Φ(√2 d + x) ^ k dN(0,1)(x)` is Dunnett's integral. It is continuous and,
for `k ≥ 1`, strictly increasing in `d`; `dunnettCDF 1 = Φ`. For `k ≥ 1` and `0 < α < 1`,
`dunnettCrit k α` is the unique `d` with `dunnettCDF k d = 1 - α`
(`dunnettCDF_dunnettCrit`, `eq_dunnettCrit`). It is non-decreasing in `k`
(`dunnettCrit_mono`) and at most any Bonferroni critical value (`dunnettCrit_le_of_bonferroni`).

## The model

`X₀` and `X j` are measurable, `X₀` is independent of the vector `(X j)`, the `X j` are
mutually independent, `X₀` is standard normal, and the comparison statistics are
`Z j = (X j - X₀) / √2 + μ j`.

* `measure_forall_manyToOne_le`: if `X i` is standard normal for `i ∈ I`, then
  `P (∀ i ∈ I, (X i - X₀) / √2 ≤ d) = dunnettCDF |I| d`.
* `fwer_dunnettSingleStep_le`, `fwer_dunnettSingleStep_eq`: single-step Dunnett.
* `fwer_dunnettStepDown_le`, `dunnettStepDown_eq_stepDownMax`,
  `dunnettSingleStep_subset_dunnettStepDown`: step-down Dunnett.
* `measure_dunnett_lowerBounds`: simultaneous lower confidence bounds, exact coverage.

Known variance, balanced design, one-sided comparisons only.
-/

open MeasureTheory Finset ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

/-! ### Closed max-statistic tests -/

section Generic

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- Max-statistic local test of the intersection hypothesis `I`: reject when some statistic
in `I` exceeds the critical value `c I`. -/
def maxLocal (T : ι → Ω → ℝ) (c : Finset ι → ℝ) (I : Finset ι) (ω : Ω) : Prop :=
  ∃ i ∈ I, c I < T i ω

/-- Critical values that do not increase when hypotheses are removed, as long as some remain. -/
def MonotoneCrit (c : Finset ι → ℝ) : Prop :=
  ∀ J I : Finset ι, J.Nonempty → J ⊆ I → c J ≤ c I

/-- The closed max-statistic test controls the family-wise error rate as soon as the local
test of the true intersection hypothesis has level `α`. -/
theorem fwer_closedTest_maxLocal_le (P : Measure Ω) (T : ι → Ω → ℝ) (c : Finset ι → ℝ)
    (H₀ : Finset ι) (α : ℝ≥0∞) (h : P {ω | maxLocal T c H₀ ω} ≤ α) :
    fwer P H₀ (closedTest (maxLocal T c)) ≤ α :=
  fwer_closedTest_le P _ H₀ α h

open Classical in
/-- Step-down max-statistic procedure, written without sorting: `i` is rejected when every
`j` whose statistic is at least `T i` exceeds the critical value of the set of hypotheses
whose statistics are at most `T j`. Tied statistics are treated alike. -/
noncomputable def stepDownMax (T : ι → Ω → ℝ) (c : Finset ι → ℝ) (ω : Ω) : Finset ι :=
  {i | ∀ j, T i ω ≤ T j ω → c {l | T l ω ≤ T j ω} < T j ω}

omit [MeasurableSpace Ω] in
/-- **Step-down shortcut.** With monotone critical values the closed max-statistic test is
the step-down procedure. -/
theorem closedTest_maxLocal_eq_stepDownMax {c : Finset ι → ℝ} (hc : MonotoneCrit c)
    (T : ι → Ω → ℝ) (ω : Ω) :
    closedTest (maxLocal T c) ω = stepDownMax T c ω := by
  classical
  ext i
  simp only [closedTest, stepDownMax, mem_filter, mem_univ, true_and]
  constructor
  · intro h j hij
    obtain ⟨l, hl, hlt⟩ := h {l | T l ω ≤ T j ω} (by simp [hij])
    exact hlt.trans_le (by simpa using hl)
  · intro h I hiI
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image I (fun j => T j ω) ⟨i, hiI⟩
    refine ⟨j, hj, lt_of_le_of_lt (hc I _ ⟨i, hiI⟩ fun l hl => ?_) (h j (hjmax i hiI))⟩
    simpa using hjmax l hl

omit [MeasurableSpace Ω] in
/-- With monotone critical values, the single-step procedure with the critical value of the
whole family rejects no more than the closed test. -/
theorem singleStep_subset_closedTest_maxLocal {c : Finset ι → ℝ} (hc : MonotoneCrit c)
    (T : ι → Ω → ℝ) (ω : Ω) {i : ι} (hi : c univ < T i ω) :
    i ∈ closedTest (maxLocal T c) ω := by
  classical
  simp only [closedTest, mem_filter, mem_univ, true_and]
  exact fun I hiI => ⟨i, hiI, lt_of_le_of_lt (hc I univ ⟨i, hiI⟩ (subset_univ _)) hi⟩

/-- Sets of hypotheses that the step-down procedure can reach: start with nothing rejected and
repeatedly reject some `i` whose statistic exceeds the critical value of the set of
hypotheses not yet rejected. -/
inductive StepDownRejectable (c : Finset ι → ℝ) (t : ι → ℝ) : Finset ι → Prop
  | empty : StepDownRejectable c t ∅
  | step {R : Finset ι} {i : ι} : StepDownRejectable c t R → i ∉ R →
      c (univ \ R) < t i → StepDownRejectable c t (insert i R)

/-- A set in which no hypothesis can be rejected. -/
def MaxStuck (c : Finset ι → ℝ) (t : ι → ℝ) (J : Finset ι) : Prop :=
  ∀ i ∈ J, t i ≤ c J

omit [MeasurableSpace Ω] in
/-- The closed max-statistic test rejects exactly the hypotheses that lie in no stuck set. -/
theorem mem_closedTest_maxLocal_iff (T : ι → Ω → ℝ) (c : Finset ι → ℝ) (ω : Ω) (i : ι) :
    i ∈ closedTest (maxLocal T c) ω ↔
      ∀ J : Finset ι, MaxStuck c (fun j => T j ω) J → i ∉ J := by
  classical
  simp only [closedTest, mem_filter, mem_univ, true_and]
  constructor
  · rintro h J hJ hiJ
    obtain ⟨l, hl, hlt⟩ := h J hiJ
    exact absurd hlt (not_lt.mpr (hJ l hl))
  · intro h I hiI
    by_contra hcon
    refine h I (fun l hl => ?_) hiI
    by_contra hl'
    exact hcon ⟨l, hl, not_le.mp hl'⟩

/-- With monotone critical values, a stuck set never meets a set rejected step-down. -/
theorem StepDownRejectable.disjoint_maxStuck {c : Finset ι → ℝ} (hc : MonotoneCrit c)
    {t : ι → ℝ} {R : Finset ι} (hR : StepDownRejectable c t R) {J : Finset ι}
    (hJ : MaxStuck c t J) : Disjoint R J := by
  induction hR with
  | empty => exact Finset.disjoint_empty_left _
  | @step R i _ hiR hlt ih =>
    rw [Finset.disjoint_insert_left]
    refine ⟨fun hiJ => ?_, ih⟩
    have hsub : J ⊆ univ \ R := fun l hl =>
      mem_sdiff.mpr ⟨mem_univ _, fun hlR => (Finset.disjoint_left.mp ih hlR) hl⟩
    exact absurd (hlt.trans_le (hJ i hiJ)) (not_lt.mpr (hc J _ ⟨i, hiJ⟩ hsub))

omit [MeasurableSpace Ω] in
/-- Soundness of the sequential form: everything it rejects is rejected by the closed test. -/
theorem StepDownRejectable.subset_closedTest {c : Finset ι → ℝ} (hc : MonotoneCrit c)
    (T : ι → Ω → ℝ) (ω : Ω) {R : Finset ι} (hR : StepDownRejectable c (fun j => T j ω) R) :
    R ⊆ closedTest (maxLocal T c) ω := by
  intro i hi
  rw [mem_closedTest_maxLocal_iff]
  intro J hJ hiJ
  exact Finset.disjoint_left.mp (hR.disjoint_maxStuck hc hJ) hi hiJ

omit [MeasurableSpace Ω] in
/-- Completeness of the sequential form: once it can reject nothing more, it has rejected
exactly what the closed test rejects, whatever order it proceeded in. -/
theorem closedTest_maxLocal_eq_of_stepDownRejectable_of_maxStuck {c : Finset ι → ℝ}
    (hc : MonotoneCrit c) (T : ι → Ω → ℝ) (ω : Ω) {R : Finset ι}
    (hR : StepDownRejectable c (fun j => T j ω) R)
    (hstuck : MaxStuck c (fun j => T j ω) (univ \ R)) :
    closedTest (maxLocal T c) ω = R := by
  refine Finset.Subset.antisymm (fun i hi => ?_) (hR.subset_closedTest hc T ω)
  by_contra hiR
  exact (mem_closedTest_maxLocal_iff T c ω i).mp hi _ hstuck (mem_sdiff.mpr ⟨mem_univ _, hiR⟩)

/-- The sequential procedure always terminates: some reachable set has a stuck complement. -/
theorem exists_stepDownRejectable_maxStuck (c : Finset ι → ℝ) (t : ι → ℝ) :
    ∃ R, StepDownRejectable c t R ∧ MaxStuck c t (univ \ R) := by
  suffices h : ∀ n : ℕ, ∀ R, StepDownRejectable c t R → (univ \ R).card = n →
      ∃ R', StepDownRejectable c t R' ∧ MaxStuck c t (univ \ R') from
    h _ ∅ .empty rfl
  intro n
  induction n with
  | zero =>
    intro R hR hn
    refine ⟨R, hR, fun i hi => ?_⟩
    rw [Finset.card_eq_zero] at hn
    simp [hn] at hi
  | succ n ih =>
    intro R hR hn
    by_cases hs : MaxStuck c t (univ \ R)
    · exact ⟨R, hR, hs⟩
    · simp only [MaxStuck, not_forall, not_le] at hs
      obtain ⟨i, hi, hlt⟩ := hs
      have hiR : i ∉ R := (mem_sdiff.mp hi).2
      refine ih (insert i R) (hR.step hiR hlt) ?_
      have : univ \ insert i R = (univ \ R).erase i := by
        ext l; simp only [mem_sdiff, mem_univ, mem_insert, true_and, mem_erase]; tauto
      rw [this, card_erase_of_mem hi, hn]; rfl

end Generic

/-! ### The standard normal distribution function -/

section NormalCDF

/-- The standard normal distribution function is continuous. -/
lemma continuous_cdf_gaussian : Continuous (cdf (gaussianReal 0 1)) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, (cdf (gaussianReal 0 1)).right_continuous a⟩
  rw [← continuousWithinAt_Iio_iff_Iic, (monotone_cdf _).continuousWithinAt_Iio_iff_leftLim_eq]
  have h := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, gaussianReal_singleton, eq_comm, ENNReal.ofReal_eq_zero] at h
  exact le_antisymm ((monotone_cdf _).leftLim_le le_rfl) (by linarith)

/-- The standard normal distribution function is strictly increasing. -/
lemma strictMono_cdf_gaussian : StrictMono (cdf (gaussianReal 0 1)) := by
  intro a b hab
  have h : gaussianReal 0 1 (Set.Ioc a b)
      = ENNReal.ofReal (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) := by
    have := (cdf (gaussianReal 0 1)).measure_Ioc a b
    rwa [measure_cdf] at this
  by_contra hcon
  have h0 : gaussianReal 0 1 (Set.Ioc a b) = 0 := by
    rw [h, ENNReal.ofReal_eq_zero]; linarith
  have h1 := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h1
  linarith

end NormalCDF

/-! ### Dunnett's integral -/

section Integral

/-- **Dunnett's integral** `∫ Φ(√2 d + x) ^ k dN(0,1)(x)`: the distribution function of the
maximum of `k` comparison statistics `(X j - X₀) / √2` with a shared control (see
`measure_forall_manyToOne_le`). -/
noncomputable def dunnettCDF (k : ℕ) (d : ℝ) : ℝ :=
  ∫ x, cdf (gaussianReal 0 1) (√2 * d + x) ^ k ∂(gaussianReal 0 1)

lemma measurable_dunnett_integrand (k : ℕ) (d : ℝ) :
    Measurable fun x : ℝ => cdf (gaussianReal 0 1) (√2 * d + x) ^ k :=
  ((monotone_cdf _).measurable.comp (measurable_const.add measurable_id)).pow_const k

lemma dunnett_integrand_nonneg (k : ℕ) (d x : ℝ) :
    0 ≤ cdf (gaussianReal 0 1) (√2 * d + x) ^ k :=
  pow_nonneg (cdf_nonneg _ _) _

lemma dunnett_integrand_le_one (k : ℕ) (d x : ℝ) :
    cdf (gaussianReal 0 1) (√2 * d + x) ^ k ≤ 1 :=
  pow_le_one₀ (cdf_nonneg _ _) (cdf_le_one _ _)

lemma integrable_dunnett_integrand (k : ℕ) (d : ℝ) :
    Integrable (fun x : ℝ => cdf (gaussianReal 0 1) (√2 * d + x) ^ k) (gaussianReal 0 1) :=
  Integrable.of_bound (measurable_dunnett_integrand k d).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (dunnett_integrand_nonneg k d x)]
      exact dunnett_integrand_le_one k d x)

lemma dunnettCDF_nonneg (k : ℕ) (d : ℝ) : 0 ≤ dunnettCDF k d :=
  integral_nonneg fun x => dunnett_integrand_nonneg k d x

lemma dunnettCDF_le_one (k : ℕ) (d : ℝ) : dunnettCDF k d ≤ 1 := by
  have h := integral_mono (integrable_dunnett_integrand k d)
    (integrable_const (μ := gaussianReal 0 1) (1 : ℝ)) fun x => dunnett_integrand_le_one k d x
  simpa [dunnettCDF] using h

@[simp] lemma dunnettCDF_zero (d : ℝ) : dunnettCDF 0 d = 1 := by
  simp [dunnettCDF]

/-- More comparisons make the maximum larger: `dunnettCDF` is non-increasing in `k`. -/
lemma dunnettCDF_anti {k l : ℕ} (hkl : k ≤ l) (d : ℝ) : dunnettCDF l d ≤ dunnettCDF k d :=
  integral_mono (integrable_dunnett_integrand l d) (integrable_dunnett_integrand k d) fun _ =>
    pow_le_pow_of_le_one (cdf_nonneg _ _) (cdf_le_one _ _) hkl

/-- Dunnett's integral is continuous in `d`. -/
lemma continuous_dunnettCDF (k : ℕ) : Continuous (dunnettCDF k) := by
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (fun d => (measurable_dunnett_integrand k d).aestronglyMeasurable) (fun d => ?_)
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (dunnett_integrand_nonneg k d x)]
      exact dunnett_integrand_le_one k d x
  · exact Filter.Eventually.of_forall fun x =>
      (continuous_cdf_gaussian.comp (by fun_prop)).pow k

/-- Dunnett's integral is strictly increasing in `d` when there is at least one comparison. -/
lemma strictMono_dunnettCDF {k : ℕ} (hk : 1 ≤ k) : StrictMono (dunnettCDF k) := by
  intro a b hab
  have hpt : ∀ x : ℝ, cdf (gaussianReal 0 1) (√2 * a + x) ^ k
      < cdf (gaussianReal 0 1) (√2 * b + x) ^ k := fun x =>
    pow_lt_pow_left₀ (strictMono_cdf_gaussian (by nlinarith [Real.sqrt_pos.mpr two_pos]))
      (cdf_nonneg _ _) (by omega)
  have hint : Integrable (fun x : ℝ => cdf (gaussianReal 0 1) (√2 * b + x) ^ k
      - cdf (gaussianReal 0 1) (√2 * a + x) ^ k) (gaussianReal 0 1) :=
    (integrable_dunnett_integrand k b).sub (integrable_dunnett_integrand k a)
  have hpos : 0 < ∫ x, (cdf (gaussianReal 0 1) (√2 * b + x) ^ k
      - cdf (gaussianReal 0 1) (√2 * a + x) ^ k) ∂(gaussianReal 0 1) := by
    rw [integral_pos_iff_support_of_nonneg (fun x => sub_nonneg.mpr (hpt x).le) hint]
    have : Function.support (fun x : ℝ => cdf (gaussianReal 0 1) (√2 * b + x) ^ k
        - cdf (gaussianReal 0 1) (√2 * a + x) ^ k) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (sub_pos.mpr (hpt x)).ne'
    rw [this, measure_univ]
    exact one_pos
  rw [integral_sub (integrable_dunnett_integrand k b) (integrable_dunnett_integrand k a)] at hpos
  simpa [dunnettCDF] using hpos

/-- Bernoulli's inequality for Dunnett's integral: the Bonferroni lower bound in terms of the
one-comparison integral. -/
lemma one_sub_mul_le_dunnettCDF (k : ℕ) (d : ℝ) :
    1 - k * (1 - dunnettCDF 1 d) ≤ dunnettCDF k d := by
  have h1 : Integrable (fun x : ℝ => cdf (gaussianReal 0 1) (√2 * d + x)) (gaussianReal 0 1) := by
    simpa using integrable_dunnett_integrand 1 d
  have h3 : Integrable (fun x : ℝ => cdf (gaussianReal 0 1) (√2 * d + x) - 1)
      (gaussianReal 0 1) := h1.sub (integrable_const _)
  have h2 : Integrable (fun x : ℝ => (k : ℝ) * (cdf (gaussianReal 0 1) (√2 * d + x) - 1))
      (gaussianReal 0 1) := h3.const_mul _
  have hint : Integrable (fun x : ℝ => 1 + (k : ℝ) * (cdf (gaussianReal 0 1) (√2 * d + x) - 1))
      (gaussianReal 0 1) := (integrable_const _).add h2
  have hle := integral_mono hint (integrable_dunnett_integrand k d) fun x => by
    have := one_add_mul_le_pow (a := cdf (gaussianReal 0 1) (√2 * d + x) - 1)
      (by linarith [cdf_nonneg (gaussianReal 0 1) (√2 * d + x)]) k
    simpa using this
  have hcomp : ∫ x, (1 + (k : ℝ) * (cdf (gaussianReal 0 1) (√2 * d + x) - 1)) ∂(gaussianReal 0 1)
      = 1 + k * (dunnettCDF 1 d - 1) := by
    rw [integral_add (integrable_const _) h2, integral_const_mul,
      integral_sub h1 (integrable_const _)]
    simp [dunnettCDF]
  rw [hcomp] at hle
  have : dunnettCDF k d = ∫ x, cdf (gaussianReal 0 1) (√2 * d + x) ^ k ∂(gaussianReal 0 1) := rfl
  linarith

end Integral

/-! ### The law of the maximum in the many-to-one model -/

section Model

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}

/-- In the comparison with a control, `(Xi - X₀) / √2` is standard normal. -/
lemma map_manyToOne_gaussian (P : Measure Ω) {X₀ Xi : Ω → ℝ} (h0 : Measurable X₀)
    (hi : Measurable Xi) (h0i : IndepFun X₀ Xi P) (hlaw0 : P.map X₀ = gaussianReal 0 1)
    (hlawi : P.map Xi = gaussianReal 0 1) :
    P.map (fun ω => (Xi ω - X₀ ω) / √2) = gaussianReal 0 1 := by
  have hfun : (fun ω => (Xi ω - X₀ ω) / √2)
      = fun ω => (√2)⁻¹ * (-X₀ ω) + (√2)⁻¹ * Xi ω := by
    funext ω; have := manyToOne_eq (X₀ ω) (Xi ω) 0; simpa using this
  rw [hfun]
  exact map_oneFactor_gaussian P _ Xi h0.neg hi (h0i.comp measurable_neg measurable_id)
    (map_neg_gaussian P h0 hlaw0) hlawi inv_sqrt_two_sq_add_sq

/-- **Dunnett's integral formula.** Let `X₀` and `X j` be measurable, `X₀` independent of the
vector `(X j)`, the `X j` mutually independent, `X₀` standard normal and `X i` standard normal
for `i ∈ I`. Then the probability that all comparison statistics `(X i - X₀) / √2`, `i ∈ I`,
are at most `d` is `∫ Φ(√2 d + x) ^ |I| dN(0,1)(x)`. -/
theorem measure_forall_manyToOne_le (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (I : Finset ι)
    (hlaw : ∀ i ∈ I, P.map (X i) = gaussianReal 0 1) (d : ℝ) :
    P {ω | ∀ i ∈ I, (X i ω - X₀ ω) / √2 ≤ d} = ENNReal.ofReal (dunnettCDF I.card d) := by
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr two_pos
  have hXv : Measurable fun ω j => X j ω := measurable_pi_iff.mpr hX
  set S : Set (ℝ × (ι → ℝ)) := {q | ∀ i ∈ I, q.2 i ≤ √2 * d + q.1} with hS
  have hSeq : S = ⋂ i ∈ I, {q : ℝ × (ι → ℝ) | q.2 i ≤ √2 * d + q.1} := by
    ext q; simp [hS]
  have hSm : MeasurableSet S := by
    rw [hSeq]
    refine Finset.measurableSet_biInter I fun i _ => ?_
    exact measurableSet_le ((measurable_pi_apply i).comp measurable_snd)
      (measurable_const.add measurable_fst)
  have hE : {ω | ∀ i ∈ I, (X i ω - X₀ ω) / √2 ≤ d}
      = (fun ω => (X₀ ω, fun j => X j ω)) ⁻¹' S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hS]
    refine forall₂_congr fun i _ => ?_
    rw [div_le_iff₀ hs2]
    constructor <;> intro h <;> linarith
  rw [hE, ← Measure.map_apply (h0.prodMk hXv) hSm,
    (indepFun_iff_map_prod_eq_prod_map_map h0.aemeasurable hXv.aemeasurable).mp h0X,
    Measure.prod_apply hSm, hlaw0, dunnettCDF,
    ofReal_integral_eq_lintegral_ofReal (integrable_dunnett_integrand _ _)
      (Filter.Eventually.of_forall fun x => dunnett_integrand_nonneg _ _ x)]
  refine lintegral_congr fun x => ?_
  rw [Measure.map_apply hXv (measurable_prodMk_left hSm)]
  have hset : (fun ω j => X j ω) ⁻¹' (Prod.mk x ⁻¹' S)
      = ⋂ i ∈ I, (X i) ⁻¹' Set.Iic (√2 * d + x) := by
    ext ω; simp [hS]
  rw [hset, hindep.meas_biInter fun i _ => ⟨_, measurableSet_Iic, rfl⟩]
  have hfac : ∀ i ∈ I, P ((X i) ⁻¹' Set.Iic (√2 * d + x))
      = ENNReal.ofReal (cdf (gaussianReal 0 1) (√2 * d + x)) := fun i hi => by
    rw [← Measure.map_apply (hX i) measurableSet_Iic, hlaw i hi, ofReal_cdf]
  rw [Finset.prod_congr rfl hfac, Finset.prod_const, ENNReal.ofReal_pow (cdf_nonneg _ _)]

/-- The complementary form: the probability that some comparison statistic in `I` exceeds
`d` is `1 - dunnettCDF |I| d`. -/
theorem measure_exists_manyToOne_gt (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (I : Finset ι)
    (hlaw : ∀ i ∈ I, P.map (X i) = gaussianReal 0 1) (d : ℝ) :
    P {ω | ∃ i ∈ I, d < (X i ω - X₀ ω) / √2} = ENNReal.ofReal (1 - dunnettCDF I.card d) := by
  have hm : MeasurableSet {ω | ∀ i ∈ I, (X i ω - X₀ ω) / √2 ≤ d} := by
    have : {ω | ∀ i ∈ I, (X i ω - X₀ ω) / √2 ≤ d}
        = ⋂ i ∈ I, {ω | (X i ω - X₀ ω) / √2 ≤ d} := by ext ω; simp
    rw [this]
    exact Finset.measurableSet_biInter I fun i _ =>
      measurableSet_le (((hX i).sub h0).div_const _) measurable_const
  have hc : {ω | ∃ i ∈ I, d < (X i ω - X₀ ω) / √2}
      = {ω | ∀ i ∈ I, (X i ω - X₀ ω) / √2 ≤ d}ᶜ := by
    ext ω; simp
  rw [hc, prob_compl_eq_one_sub hm,
    measure_forall_manyToOne_le P X₀ X h0 hX h0X hindep hlaw0 I hlaw d,
    ENNReal.ofReal_sub _ (dunnettCDF_nonneg _ _), ENNReal.ofReal_one]

/-- With one comparison, Dunnett's integral is the standard normal distribution function. -/
theorem dunnettCDF_one (d : ℝ) : dunnettCDF 1 d = cdf (gaussianReal 0 1) d := by
  let P : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hfst : P.map Prod.fst = gaussianReal 0 1 := by simp [P]
  have hsnd : P.map Prod.snd = gaussianReal 0 1 := by simp [P]
  have hind : IndepFun (Prod.fst : ℝ × ℝ → ℝ) (fun ω (_ : Unit) => ω.2) P :=
    indepFun_prod (X := (id : ℝ → ℝ)) (Y := fun (y : ℝ) (_ : Unit) => y) measurable_id
      (measurable_pi_iff.mpr fun _ => measurable_id)
  have hind' : IndepFun (Prod.fst : ℝ × ℝ → ℝ) (Prod.snd : ℝ × ℝ → ℝ) P :=
    indepFun_prod (X := (id : ℝ → ℝ)) (Y := (id : ℝ → ℝ)) measurable_id measurable_id
  have h := measure_forall_manyToOne_le P Prod.fst (fun (_ : Unit) => Prod.snd) measurable_fst
    (fun _ => measurable_snd) hind iIndepFun.of_subsingleton hfst univ (fun _ _ => hsnd) d
  have hset : {ω : ℝ × ℝ | ∀ i ∈ (univ : Finset Unit), (ω.2 - ω.1) / √2 ≤ d}
      = (fun ω : ℝ × ℝ => (ω.2 - ω.1) / √2) ⁻¹' Set.Iic d := by
    ext ω; simp
  have hmf : Measurable fun ω : ℝ × ℝ => (ω.2 - ω.1) / √2 :=
    (measurable_snd.sub measurable_fst).div_const _
  rw [hset, ← Measure.map_apply hmf
    measurableSet_Iic, map_manyToOne_gaussian P measurable_fst measurable_snd hind' hfst hsnd,
    ← ofReal_cdf] at h
  have h' := (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ _) (dunnettCDF_nonneg _ _)).mp h
  simpa using h'.symm

end Model

/-! ### Dunnett's critical values -/

section Crit

/-- For `k ≥ 1` comparisons and `0 < α < 1` the equation `dunnettCDF k d = 1 - α` has a
solution. -/
theorem exists_dunnettCDF_eq {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ d, dunnettCDF k d = 1 - α := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually_lt_const
    (show (0 : ℝ) < 1 - α by linarith)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually_const_lt
    (show 1 - α / k < 1 by linarith [div_pos hα0 hkpos])).exists
  have hlo : dunnettCDF k a ≤ 1 - α := by
    have := dunnettCDF_anti hk a
    rw [dunnettCDF_one] at this
    linarith
  have hhi : 1 - α ≤ dunnettCDF k b := by
    have := one_sub_mul_le_dunnettCDF k b
    rw [dunnettCDF_one] at this
    have h2 : (k : ℝ) * (1 - cdf (gaussianReal 0 1) b) ≤ k * (α / k) :=
      mul_le_mul_of_nonneg_left (by linarith) hkpos.le
    rw [mul_div_cancel₀ _ hkpos.ne'] at h2
    linarith
  obtain ⟨d, -, hd⟩ := intermediate_value_uIcc (continuous_dunnettCDF k).continuousOn
    (Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩) : 1 - α ∈ Set.uIcc (dunnettCDF k a) (dunnettCDF k b))
  exact ⟨d, hd⟩

open Classical in
/-- **Dunnett's critical value** for `k` one-sided comparisons with a shared control at level
`α`: the solution `d` of `∫ Φ(√2 d + x) ^ k dN(0,1)(x) = 1 - α`. It is meaningful for `k ≥ 1`
and `0 < α < 1`; otherwise the value is `0` unless a solution happens to exist. -/
noncomputable def dunnettCrit (k : ℕ) (α : ℝ) : ℝ :=
  if h : ∃ d, dunnettCDF k d = 1 - α then h.choose else 0

/-- The defining equation of Dunnett's critical value. -/
theorem dunnettCDF_dunnettCrit {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    dunnettCDF k (dunnettCrit k α) = 1 - α := by
  have h := exists_dunnettCDF_eq hk hα0 hα1
  simp only [dunnettCrit, h, ↓reduceDIte]
  exact h.choose_spec

/-- Dunnett's critical value is the only solution of its defining equation. -/
theorem eq_dunnettCrit {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {d : ℝ}
    (hd : dunnettCDF k d = 1 - α) : d = dunnettCrit k α :=
  (strictMono_dunnettCDF hk).injective (hd.trans (dunnettCDF_dunnettCrit hk hα0 hα1).symm)

/-- With a single comparison Dunnett's critical value is the normal quantile `z_{1-α}`. -/
theorem cdf_dunnettCrit_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    cdf (gaussianReal 0 1) (dunnettCrit 1 α) = 1 - α := by
  rw [← dunnettCDF_one, dunnettCDF_dunnettCrit le_rfl hα0 hα1]

/-- Dunnett's critical value is non-decreasing in the number of comparisons. -/
theorem dunnettCrit_mono {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) : dunnettCrit k α ≤ dunnettCrit l α := by
  by_contra hcon
  have h1 := strictMono_dunnettCDF hk (not_le.mp hcon)
  have h2 := dunnettCDF_anti hkl (dunnettCrit l α)
  rw [dunnettCDF_dunnettCrit hk hα0 hα1] at h1
  rw [dunnettCDF_dunnettCrit (hk.trans hkl) hα0 hα1] at h2
  linarith

/-- **Dunnett is at least as powerful as Bonferroni.** Any `z` with `1 - Φ(z) ≤ α / k` (in
particular the Bonferroni critical value `z_{1 - α/k}`) is at least Dunnett's critical
value. -/
theorem dunnettCrit_le_of_bonferroni {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {z : ℝ} (hz : 1 - cdf (gaussianReal 0 1) z ≤ α / k) : dunnettCrit k α ≤ z := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h := one_sub_mul_le_dunnettCDF k z
  rw [dunnettCDF_one] at h
  have h2 : (k : ℝ) * (1 - cdf (gaussianReal 0 1) z) ≤ k * (α / k) :=
    mul_le_mul_of_nonneg_left hz hkpos.le
  rw [mul_div_cancel₀ _ hkpos.ne'] at h2
  rw [← (strictMono_dunnettCDF hk).le_iff_le, dunnettCDF_dunnettCrit hk hα0 hα1]
  linarith

/-- Dunnett's critical values, as a function of the set of hypotheses, are monotone on
non-empty sets. -/
theorem monotoneCrit_dunnettCrit {ι : Type*} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    MonotoneCrit fun I : Finset ι => dunnettCrit I.card α :=
  fun _ _ hJ hJI => dunnettCrit_mono (Finset.card_pos.mpr hJ) (Finset.card_le_card hJI) hα0 hα1

end Crit

/-! ### Single-step and step-down Dunnett procedures -/

section Procedures

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **Level of the Dunnett local test under composite nulls.** In the many-to-one model, if
`X i` is standard normal and `μ i ≤ 0` for `i` in a non-empty set `I`, and `c` is at least
Dunnett's critical value for `|I|` comparisons, then some `Z i = (X i - X₀) / √2 + μ i`,
`i ∈ I`, exceeds `c` with probability at most `α`. -/
theorem measure_maxLocal_dunnett_le (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (μ : ι → ℝ) (I : Finset ι) (hI : I.Nonempty)
    (hlaw : ∀ i ∈ I, P.map (X i) = gaussianReal 0 1) (hμ : ∀ i ∈ I, μ i ≤ 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : dunnettCrit I.card α ≤ c) :
    P {ω | ∃ i ∈ I, c < (X i ω - X₀ ω) / √2 + μ i} ≤ ENNReal.ofReal α := by
  have hsub : {ω | ∃ i ∈ I, c < (X i ω - X₀ ω) / √2 + μ i}
      ⊆ {ω | ∃ i ∈ I, c < (X i ω - X₀ ω) / √2} := by
    rintro ω ⟨i, hi, hlt⟩
    exact ⟨i, hi, by linarith [hμ i hi]⟩
  refine (measure_mono hsub).trans ?_
  rw [measure_exists_manyToOne_gt P X₀ X h0 hX h0X hindep hlaw0 I hlaw c]
  refine ENNReal.ofReal_le_ofReal ?_
  have hk := Finset.card_pos.mpr hI
  have := (strictMono_dunnettCDF hk).monotone hc
  rw [dunnettCDF_dunnettCrit hk hα0 hα1] at this
  linarith

/-- Single-step Dunnett procedure: reject `i` when `T i` exceeds Dunnett's critical value for
all `m` comparisons. -/
noncomputable def dunnettSingleStep (α : ℝ) (T : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | dunnettCrit (Fintype.card ι) α < T i ω}

/-- Step-down Dunnett procedure: the closed test whose local test of `I` compares the largest
statistic in `I` with Dunnett's critical value for `|I|` comparisons. -/
noncomputable def dunnettStepDown (α : ℝ) (T : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  closedTest (maxLocal T fun I => dunnettCrit I.card α) ω

omit [MeasurableSpace Ω] in
/-- The step-down Dunnett procedure rejects everything the single-step procedure rejects. -/
theorem dunnettSingleStep_subset_dunnettStepDown {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (T : ι → Ω → ℝ) (ω : Ω) : dunnettSingleStep α T ω ⊆ dunnettStepDown α T ω := by
  intro i hi
  refine singleStep_subset_closedTest_maxLocal (monotoneCrit_dunnettCrit hα0 hα1) T ω ?_
  simpa [dunnettSingleStep] using hi

omit [MeasurableSpace Ω] in
/-- The step-down Dunnett procedure in step-down form (see `stepDownMax`). -/
theorem dunnettStepDown_eq_stepDownMax {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (T : ι → Ω → ℝ) (ω : Ω) :
    dunnettStepDown α T ω = stepDownMax T (fun I => dunnettCrit I.card α) ω :=
  closedTest_maxLocal_eq_stepDownMax (monotoneCrit_dunnettCrit hα0 hα1) T ω

/-- **Step-down Dunnett (Marcus, Peritz and Gabriel 1976; Dunnett and Tamhane 1991)** controls
the family-wise error rate at level `α` for the composite one-sided nulls `μ i ≤ 0`. -/
theorem fwer_dunnettStepDown_le (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (μ : ι → ℝ) (H₀ : Finset ι)
    (hlaw : ∀ i ∈ H₀, P.map (X i) = gaussianReal 0 1) (hμ : ∀ i ∈ H₀, μ i ≤ 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    fwer P H₀ (dunnettStepDown α fun j ω => (X j ω - X₀ ω) / √2 + μ j)
      ≤ ENNReal.ofReal α := by
  rcases H₀.eq_empty_or_nonempty with rfl | hne
  · simp [fwer]
  · exact fwer_closedTest_le P _ H₀ _
      (measure_maxLocal_dunnett_le P X₀ X h0 hX h0X hindep hlaw0 μ H₀ hne hlaw hμ hα0 hα1
        le_rfl)

/-- **Single-step Dunnett (Dunnett 1955)** controls the family-wise error rate at level `α`
for the composite one-sided nulls `μ i ≤ 0`, whatever the other shifts are. -/
theorem fwer_dunnettSingleStep_le (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (μ : ι → ℝ) (H₀ : Finset ι)
    (hlaw : ∀ i ∈ H₀, P.map (X i) = gaussianReal 0 1) (hμ : ∀ i ∈ H₀, μ i ≤ 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    fwer P H₀ (dunnettSingleStep α fun j ω => (X j ω - X₀ ω) / √2 + μ j)
      ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans
    (fwer_dunnettStepDown_le P X₀ X h0 hX h0X hindep hlaw0 μ H₀ hlaw hμ hα0 hα1)
  rintro ω ⟨i, hi, hrej⟩
  exact ⟨i, hi, dunnettSingleStep_subset_dunnettStepDown hα0 hα1 _ ω hrej⟩

omit [DecidableEq ι] in
/-- Under the global point null (all `X i` standard normal, all `μ i = 0`, at least one
comparison) the single-step Dunnett procedure has family-wise error rate exactly `α`. -/
theorem fwer_dunnettSingleStep_eq [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → ℝ) (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    fwer P univ (dunnettSingleStep α fun j ω => (X j ω - X₀ ω) / √2 + (0 : ℝ))
      = ENNReal.ofReal α := by
  have hset : {ω | ∃ i ∈ (univ : Finset ι),
      i ∈ dunnettSingleStep α (fun j ω => (X j ω - X₀ ω) / √2 + (0 : ℝ)) ω}
      = {ω | ∃ i ∈ (univ : Finset ι), dunnettCrit (Fintype.card ι) α < (X i ω - X₀ ω) / √2} := by
    ext ω; simp [dunnettSingleStep]
  rw [fwer, hset, measure_exists_manyToOne_gt P X₀ X h0 hX h0X hindep hlaw0 univ
    (fun i _ => hlaw i), Finset.card_univ,
    dunnettCDF_dunnettCrit Fintype.card_pos hα0 hα1, sub_sub_cancel]

omit [DecidableEq ι] in
/-- **Simultaneous lower confidence bounds.** If all `X i` are standard normal (and there is
at least one comparison), then for every vector of effects `μ` the bounds
`Z i - dunnettCrit m α` lie below `μ i` for all `i` simultaneously with probability exactly
`1 - α`. -/
theorem measure_dunnett_lowerBounds [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → ℝ) (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    (μ : ι → ℝ) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    P {ω | ∀ i, (X i ω - X₀ ω) / √2 + μ i - dunnettCrit (Fintype.card ι) α ≤ μ i}
      = ENNReal.ofReal (1 - α) := by
  have hset : {ω | ∀ i, (X i ω - X₀ ω) / √2 + μ i - dunnettCrit (Fintype.card ι) α ≤ μ i}
      = {ω | ∀ i ∈ (univ : Finset ι), (X i ω - X₀ ω) / √2 ≤ dunnettCrit (Fintype.card ι) α} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_univ, true_implies]
    refine forall_congr' fun i => ?_
    constructor <;> intro h <;> linarith
  rw [hset, measure_forall_manyToOne_le P X₀ X h0 hX h0X hindep hlaw0 univ (fun i _ => hlaw i),
    Finset.card_univ, dunnettCDF_dunnettCrit Fintype.card_pos hα0 hα1]

end Procedures

end Applied.MultipleTesting
