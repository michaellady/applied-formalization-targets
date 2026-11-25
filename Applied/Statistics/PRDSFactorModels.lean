import Applied.Statistics.PRDSCommonFactor
import Applied.Statistics.PValues

/-!
# Positive dependence in factor models: unequal loadings, blocks, comparisons with a control

`IsPRDSOn` (see `Applied/Statistics/PRDS.lean`) is the conditioning-on-`p i ≤ t` form of
positive regression dependence (the definition of Ramdas et al. 2019; sometimes called weak
PRDS), not the
definition of Benjamini and Yekutieli, which conditions on `p i = t`. Everything below is
about this form.

This file widens the one-factor results of `Applied/Statistics/PRDSCommonFactor.lean` and
turns them into end-to-end statements about Benjamini–Hochberg, Simes, Hochberg and Hommel for
one-sided z-tests, `p j = 1 - Φ (Z j)`.

## One common factor, unequal loadings

`Z j = a j * W + b j * ε j + μ j`, with `W` independent of the mutually independent `ε j` and
`a j ≥ 0`. With `W`, `ε j` standard normal and `b j = √(1 - a j ^ 2)`, every null statistic is
standard normal and two statistics have covariance `a i * a j`.

* `isPRDSOn_oneFactor_zTests`, `isPRDSOn_oneFactor_zTests_restrict` (the condition on every
  subfamily, as needed by Hochberg and Hommel);
* `map_oneFactor_gaussian`, `covariance_oneFactor`;
* `fdr_bhReject_le_oneFactor_zTests`, `measure_simes_le_oneFactor_zTests`,
  `fwer_hochberg_le_oneFactor_zTests`, `fwer_hommel_le_oneFactor_zTests`.

## Independent groups, one factor per group

`Z j = a j * W (g j) + b j * ε j + μ j`, where `g : ι → κ` assigns each hypothesis to a group and
all of the factors `W k` and noises `ε j` are mutually independent.

* `isPRDSOn_groupFactor_gaussian`, `isPRDSOn_groupFactor_zTests`,
  `fdr_bhReject_le_groupFactor_zTests`, `fwer_hochberg_le_groupFactor_zTests`.

## Many-to-one comparisons with a shared control (Dunnett-type)

`Z j = (X j - X₀) / √2 + μ j` with independent standard normal `X₀, X j`. This is the one-factor
model with factor `-X₀` and loadings `1 / √2` (pairwise correlation `1 / 2`).

* `isPRDSOn_manyToOne`, `fdr_bhReject_le_manyToOne`, `fwer_hochberg_le_manyToOne`,
  `fwer_hommel_le_manyToOne`, `covariance_manyToOne`.
-/

open MeasureTheory Finset ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω]

section Normal

/-- If `W` and `e` are independent standard normal variables and `a ^ 2 + b ^ 2 = 1`, then
`a * W + b * e` is standard normal. -/
theorem map_oneFactor_gaussian (P : Measure Ω) (W e : Ω → ℝ) (hW : Measurable W)
    (he : Measurable e) (hWe : IndepFun W e P) (hlawW : P.map W = gaussianReal 0 1)
    (hlawe : P.map e = gaussianReal 0 1) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    P.map (fun ω => a * W ω + b * e ω) = gaussianReal 0 1 := by
  have h1 := gaussianReal_const_mul (⟨hW.aemeasurable, hlawW⟩ : HasLaw W (gaussianReal 0 1) P) a
  have h2 := gaussianReal_const_mul (⟨he.aemeasurable, hlawe⟩ : HasLaw e (gaussianReal 0 1) P) b
  have hind : (fun ω => a * W ω) ⟂ᵢ[P] (fun ω => b * e ω) :=
    hWe.comp (measurable_const_mul _) (measurable_const_mul _)
  have h := gaussianReal_add_gaussianReal_of_indepFun hind h1 h2
  have hfun : (fun ω => a * W ω + b * e ω) = (fun ω => a * W ω) + fun ω => b * e ω := rfl
  rw [hfun, h]
  have hv : (NNReal.mk (a ^ 2) (sq_nonneg _)) * 1 + (NNReal.mk (b ^ 2) (sq_nonneg _)) * 1 = 1 := by
    apply NNReal.eq
    simp only [mul_one, NNReal.coe_add, NNReal.coe_mk, NNReal.coe_one, hab]
  rw [hv]
  simp

/-- The one-sided p-value `1 - Φ (a * W + b * e)` is valid when `W`, `e` are independent
standard normal and `a ^ 2 + b ^ 2 = 1`. -/
theorem isValidPValue_oneFactor_zTest (P : Measure Ω) (W e : Ω → ℝ) (hW : Measurable W)
    (he : Measurable e) (hWe : IndepFun W e P) (hlawW : P.map W = gaussianReal 0 1)
    (hlawe : P.map e = gaussianReal 0 1) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    IsValidPValue P fun ω => 1 - cdf (gaussianReal 0 1) (a * W ω + b * e ω) :=
  isValidPValue_zTest_upper P _ ((hW.const_mul _).add (he.const_mul _))
    (map_oneFactor_gaussian P W e hW he hWe hlawW hlawe hab)

/-- Two statistics `a W + b e₁` and `a' W + b' e₂` of a one-factor model have covariance
`a * a'`, when `W`, `e₁`, `e₂` are pairwise independent, square-integrable and `Var W = 1`.
With `a ^ 2 + b ^ 2 = a' ^ 2 + b' ^ 2 = 1` and standard normal variables both statistics have
variance one, so `a * a'` is their correlation. -/
theorem covariance_oneFactor (P : Measure Ω) [IsProbabilityMeasure P] (W e₁ e₂ : Ω → ℝ)
    (hW : MemLp W 2 P) (he₁ : MemLp e₁ 2 P) (he₂ : MemLp e₂ 2 P)
    (hWe₁ : IndepFun W e₁ P) (hWe₂ : IndepFun W e₂ P) (he : IndepFun e₁ e₂ P)
    (hvar : Var[W; P] = 1) (a b a' b' : ℝ) :
    cov[fun ω => a * W ω + b * e₁ ω, fun ω => a' * W ω + b' * e₂ ω; P] = a * a' := by
  have hA : MemLp (fun ω => a * W ω) 2 P := hW.const_mul _
  have hA' : MemLp (fun ω => a' * W ω) 2 P := hW.const_mul _
  have hB₁ : MemLp (fun ω => b * e₁ ω) 2 P := he₁.const_mul _
  have hB₂ : MemLp (fun ω => b' * e₂ ω) 2 P := he₂.const_mul _
  change cov[(fun ω => a * W ω) + (fun ω => b * e₁ ω),
    (fun ω => a' * W ω) + (fun ω => b' * e₂ ω); P] = a * a'
  rw [covariance_add_left hA hB₁ (hA'.add hB₂), covariance_add_right hA hA' hB₂,
    covariance_add_right hB₁ hA' hB₂]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  rw [covariance_self hW.aestronglyMeasurable.aemeasurable, hvar,
    hWe₂.covariance_eq_zero hW he₂, hWe₁.symm.covariance_eq_zero he₁ hW,
    he.covariance_eq_zero he₁ he₂]
  ring

/-- Loadings `a` and `√(1 - a²)` have squares summing to one (unit variance). -/
lemma sq_add_sq_sqrt_one_sub {a : ℝ} (ha : a ^ 2 ≤ 1) : a ^ 2 + √(1 - a ^ 2) ^ 2 = 1 := by
  rw [Real.sq_sqrt (by linarith)]; ring

/-- For `0 ≤ a < 1` the idiosyncratic loading `√(1 - a²)` is non-zero. -/
lemma sqrt_one_sub_sq_ne_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) : √(1 - a ^ 2) ≠ 0 :=
  (Real.sqrt_pos.mpr (by nlinarith)).ne'

/-- `a² ≤ 1` for `0 ≤ a < 1`. -/
lemma sq_le_one_of_lt_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) : a ^ 2 ≤ 1 := by nlinarith

end Normal

section OneFactor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **One factor, unequal loadings.** Let `Z j = a j * W + b j * ε j + μ j` with `W` (of any
law) independent of the mutually independent `ε j`, and non-negative loadings `a j`. If for every
true null `i` the noise `ε i` is standard normal and `b i ≠ 0`, the one-sided p-values
`1 - Φ (Z j)` are positively regression dependent on the true nulls. -/
theorem isPRDSOn_oneFactor_zTests (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (a b μ : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (H₀ : Finset ι) (hb : ∀ i ∈ H₀, b i ≠ 0)
    (hlaw : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P (fun j ω => 1 - cdf (gaussianReal 0 1) (a j * W ω + b j * ε j ω + μ j)) H₀ :=
  isPRDSOn_gaussian_commonFactor P W ε hW hε hWε hindep a b ha
    (fun j z => 1 - cdf (gaussianReal 0 1) (z + μ j))
    (fun j => antitone_one_sub_cdf_gaussian_add (μ j)) H₀ hb hlaw

omit [Fintype ι] in
/-- **The one-factor structure restricts to subfamilies.** For any set `S` of hypotheses
whose noises are standard normal with `b i ≠ 0`, the p-values indexed by `S`, as a family on
their own, are positively regression dependent on all of `S`. This is the hypothesis of the
Hochberg and Hommel theorems with `S` the set of true nulls. -/
theorem isPRDSOn_oneFactor_zTests_restrict (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (a b μ : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (S : Finset ι) (hb : ∀ i ∈ S, b i ≠ 0)
    (hlaw : ∀ i ∈ S, P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P (fun (j : S) ω => 1 - cdf (gaussianReal 0 1) (a j * W ω + b j * ε j ω + μ j))
      univ := by
  have hres : Measurable fun (v : ι → ℝ) (j : S) => v j :=
    measurable_pi_iff.mpr fun j => measurable_pi_apply j.1
  exact isPRDSOn_oneFactor_zTests (ι := S) P W (fun j => ε j) hW (fun j => hε j)
    (hWε.comp measurable_id hres) (hindep.precomp Subtype.val_injective)
    (fun j => a j) (fun j => b j) (fun j => μ j) (fun j => ha j) univ
    (fun j _ => hb j j.2) (fun j _ => hlaw j j.2)

/-- The one-sided z-test p-value in the one-factor model is measurable. -/
lemma measurable_oneFactor_zTest {W e : Ω → ℝ} (hW : Measurable W) (he : Measurable e)
    (a b m : ℝ) :
    Measurable fun ω => 1 - cdf (gaussianReal 0 1) (a * W ω + b * e ω + m) :=
  measurable_one_sub_cdf_gaussian.comp (((hW.const_mul _).add (he.const_mul _)).add
    measurable_const)

/-- Validity of the true-null p-values in the model with `b j = √(1 - a j ^ 2)`. -/
lemma isValidPValue_oneFactor_zTest_sqrt (P : Measure Ω) {W e : Ω → ℝ} (hW : Measurable W)
    (he : Measurable e) (hWe : IndepFun W e P) (hlawW : P.map W = gaussianReal 0 1)
    (hlawe : P.map e = gaussianReal 0 1) {a m : ℝ} (ha : a ^ 2 ≤ 1) (hm : m = 0) :
    IsValidPValue P fun ω => 1 - cdf (gaussianReal 0 1) (a * W ω + √(1 - a ^ 2) * e ω + m) := by
  subst hm
  simpa using isValidPValue_oneFactor_zTest P W e hW he hWe hlawW hlawe
    (sq_add_sq_sqrt_one_sub ha)

/-- **Benjamini–Hochberg for one-sided z-tests in a one-factor model with unequal non-negative
correlations.** Let `Z j = a j * W + √(1 - a j ^ 2) * ε j + μ j`, where `W` is standard normal
and independent of the mutually independent `ε j`, the loadings satisfy `a j ≥ 0` for all `j`
and `a i < 1` for the true nulls, the null noises `ε i` are standard normal and the null
shifts `μ i` vanish. Then the Benjamini–Hochberg procedure applied to `1 - Φ (Z j)` at level
`α ≥ 0` has false discovery rate at most `α m₀ / m`. -/
theorem fdr_bhReject_le_oneFactor_zTests (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (a μ : ι → ℝ) (ha0 : ∀ j, 0 ≤ a j) (H₀ : Finset ι)
    (ha1 : ∀ i ∈ H₀, a i < 1) (hlawε : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1)
    (hμ : ∀ i ∈ H₀, μ i = 0) {α : ℝ} (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j =>
        1 - cdf (gaussianReal 0 1) (a j * W ω + √(1 - a j ^ 2) * ε j ω + μ j))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) :=
  fdr_bhReject_le_of_prds P hα _
    (fun j => measurable_oneFactor_zTest hW (hε j) _ _ _) H₀
    (fun i hi => isValidPValue_oneFactor_zTest_sqrt P hW (hε i)
      (hWε.comp measurable_id (measurable_pi_apply i)) hlawW (hlawε i hi)
      (sq_le_one_of_lt_one (ha0 i) (ha1 i hi)) (hμ i hi))
    (isPRDSOn_oneFactor_zTests P W ε hW hε hWε hindep a (fun j => √(1 - a j ^ 2)) μ ha0 H₀
      (fun i hi => sqrt_one_sub_sq_ne_zero (ha0 i) (ha1 i hi)) hlawε)

/-- **Simes inequality in the one-factor model with unequal loadings.** Under the global null
(`Z j = a j * W + √(1 - a j ^ 2) * ε j`, `0 ≤ a j < 1`, all variables standard normal, `W`
independent of the mutually independent `ε j`), the Simes test at level `α ≥ 0` rejects with
probability at most `α`. -/
theorem measure_simes_le_oneFactor_zTests (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (hlawε : ∀ j, P.map (ε j) = gaussianReal 0 1)
    (a : ι → ℝ) (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j < 1) {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => 1 - cdf (gaussianReal 0 1) (a j * W ω + √(1 - a j ^ 2) * ε j ω)}
      ≤ ENNReal.ofReal α :=
  measure_one_le_bhK_le_of_prds P hα _
    (fun j => measurable_one_sub_cdf_gaussian.comp ((hW.const_mul _).add ((hε j).const_mul _)))
    (fun i => isValidPValue_oneFactor_zTest P W (ε i) hW (hε i)
      (hWε.comp measurable_id (measurable_pi_apply i)) hlawW (hlawε i)
      (sq_add_sq_sqrt_one_sub (sq_le_one_of_lt_one (ha0 i) (ha1 i))))
    (isPRDSOn_gaussian_commonFactor P W ε hW hε hWε hindep a (fun j => √(1 - a j ^ 2)) ha0
      (fun _ z => 1 - cdf (gaussianReal 0 1) z) (fun _ x y hxy => by
        have := monotone_cdf (gaussianReal 0 1) hxy
        show 1 - _ ≤ 1 - _
        linarith)
      univ (fun i _ => sqrt_one_sub_sq_ne_zero (ha0 i) (ha1 i)) (fun i _ => hlawε i))

/-- **Hochberg's procedure in the one-factor model with unequal loadings** controls the
family-wise error rate at level `α`, under the hypotheses of
`fdr_bhReject_le_oneFactor_zTests`. -/
theorem fwer_hochberg_le_oneFactor_zTests (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (a μ : ι → ℝ) (ha0 : ∀ j, 0 ≤ a j) (H₀ : Finset ι)
    (ha1 : ∀ i ∈ H₀, a i < 1) (hlawε : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1)
    (hμ : ∀ i ∈ H₀, μ i = 0) {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hochberg α fun j ω =>
        1 - cdf (gaussianReal 0 1) (a j * W ω + √(1 - a j ^ 2) * ε j ω + μ j))
      ≤ ENNReal.ofReal α :=
  fwer_hochberg_le_of_prds P hα _ (fun j => measurable_oneFactor_zTest hW (hε j) _ _ _) H₀
    (fun i hi => isValidPValue_oneFactor_zTest_sqrt P hW (hε i)
      (hWε.comp measurable_id (measurable_pi_apply i)) hlawW (hlawε i hi)
      (sq_le_one_of_lt_one (ha0 i) (ha1 i hi)) (hμ i hi))
    (isPRDSOn_oneFactor_zTests_restrict P W ε hW hε hWε hindep a (fun j => √(1 - a j ^ 2)) μ
      ha0 H₀ (fun i hi => sqrt_one_sub_sq_ne_zero (ha0 i) (ha1 i hi)) hlawε)

/-- **Hommel's procedure in the one-factor model with unequal loadings** controls the
family-wise error rate at level `α`, under the hypotheses of
`fdr_bhReject_le_oneFactor_zTests`. -/
theorem fwer_hommel_le_oneFactor_zTests (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (a μ : ι → ℝ) (ha0 : ∀ j, 0 ≤ a j) (H₀ : Finset ι)
    (ha1 : ∀ i ∈ H₀, a i < 1) (hlawε : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1)
    (hμ : ∀ i ∈ H₀, μ i = 0) {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hommel α fun j ω =>
        1 - cdf (gaussianReal 0 1) (a j * W ω + √(1 - a j ^ 2) * ε j ω + μ j))
      ≤ ENNReal.ofReal α :=
  fwer_hommel_le_of_prds P hα _ (fun j => measurable_oneFactor_zTest hW (hε j) _ _ _) H₀
    (fun i hi => isValidPValue_oneFactor_zTest_sqrt P hW (hε i)
      (hWε.comp measurable_id (measurable_pi_apply i)) hlawW (hlawε i hi)
      (sq_le_one_of_lt_one (ha0 i) (ha1 i hi)) (hμ i hi))
    (isPRDSOn_oneFactor_zTests_restrict P W ε hW hε hWε hindep a (fun j => √(1 - a j ^ 2)) μ
      ha0 H₀ (fun i hi => sqrt_one_sub_sq_ne_zero (ha0 i) (ha1 i hi)) hlawε)

end OneFactor

section GroupFactor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Independent groups, one factor per group.** Each hypothesis `j` belongs to a group
`g j`; the statistic is `c j * W (g j) + d j * ε j` with `c j ≥ 0`, and all the group factors
`W k` and noises `ε j` together are mutually independent (no assumption on the law of the
factors). Let `p j = ψ j (statistic)` with `ψ j` non-increasing. If for every true null `i` the
noise `ε i` is standard normal and `d i ≠ 0`, the p-values are positively regression dependent
on the true nulls. -/
theorem isPRDSOn_groupFactor_gaussian (P : Measure Ω) [IsProbabilityMeasure P] {κ : Type*}
    [Fintype κ] (g : ι → κ) (W : κ → Ω → ℝ) (ε : ι → Ω → ℝ) (hW : ∀ k, Measurable (W k))
    (hε : ∀ j, Measurable (ε j)) (hind : iIndepFun (Sum.elim W ε) P)
    (c d : ι → ℝ) (hc : ∀ j, 0 ≤ c j) (ψ : ι → ℝ → ℝ) (hψ : ∀ j, Antitone (ψ j))
    (H₀ : Finset ι) (hd : ∀ i ∈ H₀, d i ≠ 0)
    (hlaw : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P (fun j ω => ψ j (c j * W (g j) ω + d j * ε j ω)) H₀ := by
  classical
  have hψm : ∀ j, Measurable (ψ j) := fun j => (hψ j).measurable
  have hFm : ∀ x, Measurable (Sum.elim W ε x) := by
    rintro (k | j)
    exacts [hW k, hε j]
  have hpm : ∀ j, Measurable fun ω => ψ j (c j * W (g j) ω + d j * ε j ω) := fun j =>
    (hψm j).comp (((hW _).const_mul _).add ((hε j).const_mul _))
  rw [isPRDSOn_iff_forall_singleton]
  intro i hi
  set B : Finset ι := univ.filter fun j => g j = g i with hB
  have hiB : i ∈ B := by simp [hB]
  -- the variables driving the group of `i`, and all the others
  set inGroup : κ ⊕ ι → Prop := fun x => Sum.elim (fun k => k = g i) (fun j => g j = g i) x
    with hin
  set S : Finset (κ ⊕ ι) := univ.filter inGroup with hS
  set T : Finset (κ ⊕ ι) := univ.filter fun x => ¬ inGroup x with hT
  have hIndST := hind.indepFun_finset S T (disjoint_filter_filter_not _ _ _) hFm
  have hSW : ∀ j ∈ B, (Sum.inl (g j) : κ ⊕ ι) ∈ S := fun j hj => by
    simpa [hS, hin, hB] using hj
  have hSε : ∀ j ∈ B, (Sum.inr j : κ ⊕ ι) ∈ S := fun j hj => by
    simpa [hS, hin, hB] using hj
  have hTW : ∀ j ∉ B, (Sum.inl (g j) : κ ⊕ ι) ∈ T := fun j hj => by
    simpa [hT, hin, hB] using hj
  have hTε : ∀ j ∉ B, (Sum.inr j : κ ⊕ ι) ∈ T := fun j hj => by
    simpa [hT, hin, hB] using hj
  set φ : (S → ℝ) → B → ℝ := fun v j =>
    ψ j (c j * v ⟨Sum.inl (g j), hSW j j.2⟩ + d j * v ⟨Sum.inr j, hSε j j.2⟩) with hφdef
  set χ : (T → ℝ) → {j // j ∉ B} → ℝ := fun v j =>
    ψ j (c j * v ⟨Sum.inl (g j), hTW j j.2⟩ + d j * v ⟨Sum.inr j, hTε j j.2⟩) with hχdef
  have hφ : Measurable φ := measurable_pi_iff.mpr fun j => (hψm j).comp
    (((measurable_pi_apply _).const_mul _).add ((measurable_pi_apply _).const_mul _))
  have hχ : Measurable χ := measurable_pi_iff.mpr fun j => (hψm j).comp
    (((measurable_pi_apply _).const_mul _).add ((measurable_pi_apply _).const_mul _))
  have hindep : IndepFun (fun ω (j : B) => ψ j (c j * W (g j) ω + d j * ε j ω))
      (fun ω (j : {j // j ∉ B}) => ψ j (c j * W (g j) ω + d j * ε j ω)) P :=
    hIndST.comp hφ hχ
  refine isPRDSOn_of_indepFun_block P _ hpm B hiB hindep ?_
  -- within the group the factor is `W (g i)`
  have hfun : (fun (j : B) ω => ψ j (c j * W (g j) ω + d j * ε j ω))
      = fun (j : B) ω => ψ j (c j * W (g i) ω + d j * ε j ω) := by
    funext j ω
    rw [(mem_filter.mp j.2).2]
  rw [hfun]
  have hWB : IndepFun (W (g i)) (fun ω (j : B) => ε j ω) P := by
    set E : Finset (κ ⊕ ι) := B.map ⟨Sum.inr, Sum.inr_injective⟩ with hE
    have hmemE : ∀ j ∈ B, (Sum.inr j : κ ⊕ ι) ∈ E := fun j hj =>
      mem_map_of_mem (f := ⟨Sum.inr, Sum.inr_injective⟩) hj
    have hdisj : Disjoint ({Sum.inl (g i)} : Finset (κ ⊕ ι)) E :=
      Finset.disjoint_singleton_left.mpr (by simp [hE])
    have h1 := hind.indepFun_finset _ _ hdisj hFm
    have hm1 : Measurable fun v : ({Sum.inl (g i)} : Finset (κ ⊕ ι)) → ℝ =>
        v ⟨Sum.inl (g i), mem_singleton_self _⟩ := measurable_pi_apply _
    have hm2 : Measurable fun (v : E → ℝ) (j : B) => v ⟨Sum.inr j, hmemE j j.2⟩ :=
      measurable_pi_iff.mpr fun j => measurable_pi_apply _
    exact h1.comp hm1 hm2
  have hεB : iIndepFun (fun j : B => ε j) P :=
    hind.precomp (g := fun j : B => (Sum.inr j.1 : κ ⊕ ι))
      (fun x y h => Subtype.ext (Sum.inr_injective h))
  exact isPRDSOn_gaussian_commonFactor (ι := B) P (W (g i)) (fun j => ε j) (hW _)
    (fun j => hε j) hWB hεB (fun j => c j) (fun j => d j) (fun j => hc j) (fun j => ψ j)
    (fun j => hψ j) {⟨i, hiB⟩}
    (fun j hj => by rw [mem_singleton.mp hj]; exact hd i hi)
    (fun j hj => by rw [mem_singleton.mp hj]; exact hlaw i hi)

/-- One-sided z-tests in the group-factor model: `p j = 1 - Φ (a j * W (g j) + b j * ε j + μ j)`
are positively regression dependent on the true nulls (see `isPRDSOn_groupFactor_gaussian`). -/
theorem isPRDSOn_groupFactor_zTests (P : Measure Ω) [IsProbabilityMeasure P] {κ : Type*}
    [Fintype κ] (g : ι → κ) (W : κ → Ω → ℝ) (ε : ι → Ω → ℝ) (hW : ∀ k, Measurable (W k))
    (hε : ∀ j, Measurable (ε j)) (hind : iIndepFun (Sum.elim W ε) P)
    (a b μ : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (H₀ : Finset ι) (hb : ∀ i ∈ H₀, b i ≠ 0)
    (hlaw : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P (fun j ω => 1 - cdf (gaussianReal 0 1) (a j * W (g j) ω + b j * ε j ω + μ j))
      H₀ :=
  isPRDSOn_groupFactor_gaussian P g W ε hW hε hind a b ha
    (fun j z => 1 - cdf (gaussianReal 0 1) (z + μ j))
    (fun j => antitone_one_sub_cdf_gaussian_add (μ j)) H₀ hb hlaw

omit [Fintype ι] in
/-- The group-factor structure restricts to subfamilies: the p-values indexed by `S`, as a
family on their own, are positively regression dependent on all of `S`. -/
theorem isPRDSOn_groupFactor_zTests_restrict (P : Measure Ω) [IsProbabilityMeasure P]
    {κ : Type*} [Fintype κ] (g : ι → κ) (W : κ → Ω → ℝ) (ε : ι → Ω → ℝ)
    (hW : ∀ k, Measurable (W k)) (hε : ∀ j, Measurable (ε j))
    (hind : iIndepFun (Sum.elim W ε) P) (a b μ : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (S : Finset ι)
    (hb : ∀ i ∈ S, b i ≠ 0) (hlaw : ∀ i ∈ S, P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P (fun (j : S) ω =>
      1 - cdf (gaussianReal 0 1) (a j * W (g j) ω + b j * ε j ω + μ j)) univ := by
  have hinj : Function.Injective (Sum.map id Subtype.val : κ ⊕ S → κ ⊕ ι) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Subtype.val_injective⟩
  have h := hind.precomp hinj
  have hfam : (fun x => Sum.elim W ε (Sum.map id Subtype.val x))
      = Sum.elim W (fun j : S => ε j) := by
    funext x
    cases x <;> rfl
  rw [hfam] at h
  exact isPRDSOn_groupFactor_zTests (ι := S) P (fun j => g j) W (fun j => ε j) hW
    (fun j => hε j) h (fun j => a j) (fun j => b j) (fun j => μ j) (fun j => ha j) univ
    (fun j _ => hb j j.2) (fun j _ => hlaw j j.2)

/-- **Benjamini–Hochberg for one-sided z-tests in independent groups with one factor per
group.** Let `Z j = a j * W (g j) + √(1 - a j ^ 2) * ε j + μ j`, where the group factors `W k`
are standard normal, all the `W k` and `ε j` together are mutually independent, `a j ≥ 0` for
all `j`, and for every true null `a i < 1`, `ε i` is standard normal and `μ i = 0`. Then the
Benjamini–Hochberg procedure applied to `1 - Φ (Z j)` at level `α ≥ 0` has false discovery
rate at most `α m₀ / m`. -/
theorem fdr_bhReject_le_groupFactor_zTests (P : Measure Ω) [IsProbabilityMeasure P]
    {κ : Type*} [Fintype κ] (g : ι → κ) (W : κ → Ω → ℝ) (ε : ι → Ω → ℝ)
    (hW : ∀ k, Measurable (W k)) (hε : ∀ j, Measurable (ε j))
    (hind : iIndepFun (Sum.elim W ε) P) (hlawW : ∀ k, P.map (W k) = gaussianReal 0 1)
    (a μ : ι → ℝ) (ha0 : ∀ j, 0 ≤ a j) (H₀ : Finset ι) (ha1 : ∀ i ∈ H₀, a i < 1)
    (hlawε : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1) (hμ : ∀ i ∈ H₀, μ i = 0)
    {α : ℝ} (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j =>
        1 - cdf (gaussianReal 0 1) (a j * W (g j) ω + √(1 - a j ^ 2) * ε j ω + μ j))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) :=
  fdr_bhReject_le_of_prds P hα _ (fun j => measurable_oneFactor_zTest (hW _) (hε j) _ _ _) H₀
    (fun i hi => isValidPValue_oneFactor_zTest_sqrt P (hW _) (hε i)
      (hind.indepFun (i := Sum.inl (g i)) (j := Sum.inr i) Sum.inl_ne_inr) (hlawW _)
      (hlawε i hi) (sq_le_one_of_lt_one (ha0 i) (ha1 i hi)) (hμ i hi))
    (isPRDSOn_groupFactor_zTests P g W ε hW hε hind a (fun j => √(1 - a j ^ 2)) μ ha0 H₀
      (fun i hi => sqrt_one_sub_sq_ne_zero (ha0 i) (ha1 i hi)) hlawε)

/-- **Hochberg's procedure in the group-factor model** controls the family-wise error rate at
level `α`, under the hypotheses of `fdr_bhReject_le_groupFactor_zTests`. -/
theorem fwer_hochberg_le_groupFactor_zTests (P : Measure Ω) [IsProbabilityMeasure P]
    {κ : Type*} [Fintype κ] (g : ι → κ) (W : κ → Ω → ℝ) (ε : ι → Ω → ℝ)
    (hW : ∀ k, Measurable (W k)) (hε : ∀ j, Measurable (ε j))
    (hind : iIndepFun (Sum.elim W ε) P) (hlawW : ∀ k, P.map (W k) = gaussianReal 0 1)
    (a μ : ι → ℝ) (ha0 : ∀ j, 0 ≤ a j) (H₀ : Finset ι) (ha1 : ∀ i ∈ H₀, a i < 1)
    (hlawε : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1) (hμ : ∀ i ∈ H₀, μ i = 0)
    {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hochberg α fun j ω =>
        1 - cdf (gaussianReal 0 1) (a j * W (g j) ω + √(1 - a j ^ 2) * ε j ω + μ j))
      ≤ ENNReal.ofReal α :=
  fwer_hochberg_le_of_prds P hα _ (fun j => measurable_oneFactor_zTest (hW _) (hε j) _ _ _) H₀
    (fun i hi => isValidPValue_oneFactor_zTest_sqrt P (hW _) (hε i)
      (hind.indepFun (i := Sum.inl (g i)) (j := Sum.inr i) Sum.inl_ne_inr) (hlawW _)
      (hlawε i hi) (sq_le_one_of_lt_one (ha0 i) (ha1 i hi)) (hμ i hi))
    (isPRDSOn_groupFactor_zTests_restrict P g W ε hW hε hind a (fun j => √(1 - a j ^ 2)) μ ha0
      H₀ (fun i hi => sqrt_one_sub_sq_ne_zero (ha0 i) (ha1 i hi)) hlawε)

end GroupFactor

section ManyToOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The comparison statistic `(x - x₀) / √2 + m` in one-factor form, with factor `-x₀` and
loadings `1 / √2`. -/
lemma manyToOne_eq (x₀ x m : ℝ) : (x - x₀) / √2 + m = (√2)⁻¹ * (-x₀) + (√2)⁻¹ * x + m := by
  ring

/-- The loadings `1 / √2`, `1 / √2` have squares summing to one. -/
lemma inv_sqrt_two_sq_add_sq : ((√2)⁻¹) ^ 2 + ((√2)⁻¹) ^ 2 = 1 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- The negative of a standard normal variable is standard normal. -/
lemma map_neg_gaussian (P : Measure Ω) {X₀ : Ω → ℝ} (h0 : Measurable X₀)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) : P.map (fun ω => -X₀ ω) = gaussianReal 0 1 := by
  have : P.map (fun ω => -X₀ ω) = (P.map X₀).map (fun x => -x) :=
    (Measure.map_map measurable_neg h0).symm
  rw [this, hlaw0, gaussianReal_map_neg, neg_zero]

/-- **Many-to-one comparisons with a shared control.** Let `X₀` (control) and `X j`
(treatments) be measurable, `X₀` independent of the vector `(X j)`, the `X j` mutually
independent, and let `Z j = (X j - X₀) / √2 + μ j`. If `X i` is standard normal for every true
null `i`, the one-sided p-values `1 - Φ (Z j)` are positively regression dependent on the true
nulls. The law of `X₀` is not used. -/
theorem isPRDSOn_manyToOne (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P) (μ : ι → ℝ)
    (H₀ : Finset ι) (hlaw : ∀ i ∈ H₀, P.map (X i) = gaussianReal 0 1) :
    IsPRDSOn P (fun j ω => 1 - cdf (gaussianReal 0 1) ((X j ω - X₀ ω) / √2 + μ j)) H₀ := by
  have hfun : (fun j ω => 1 - cdf (gaussianReal 0 1) ((X j ω - X₀ ω) / √2 + μ j))
      = fun j ω => 1 - cdf (gaussianReal 0 1) ((√2)⁻¹ * (-X₀ ω) + (√2)⁻¹ * X j ω + μ j) := by
    funext j ω; rw [manyToOne_eq]
  rw [hfun]
  exact isPRDSOn_oneFactor_zTests P (fun ω => -X₀ ω) X h0.neg hX
    (h0X.comp measurable_neg measurable_id) hindep (fun _ => (√2)⁻¹) (fun _ => (√2)⁻¹) μ
    (fun _ => by positivity) H₀ (fun _ _ => by positivity) hlaw

omit [Fintype ι] in
/-- Restriction of `isPRDSOn_manyToOne` to a subfamily `S`. -/
theorem isPRDSOn_manyToOne_restrict (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P) (μ : ι → ℝ)
    (S : Finset ι) (hlaw : ∀ i ∈ S, P.map (X i) = gaussianReal 0 1) :
    IsPRDSOn P (fun (j : S) ω => 1 - cdf (gaussianReal 0 1) ((X j ω - X₀ ω) / √2 + μ j))
      univ := by
  have hfun : (fun (j : S) ω => 1 - cdf (gaussianReal 0 1) ((X j ω - X₀ ω) / √2 + μ j))
      = fun (j : S) ω =>
        1 - cdf (gaussianReal 0 1) ((√2)⁻¹ * (-X₀ ω) + (√2)⁻¹ * X j ω + μ j) := by
    funext j ω; rw [manyToOne_eq]
  rw [hfun]
  exact isPRDSOn_oneFactor_zTests_restrict P (fun ω => -X₀ ω) X h0.neg hX
    (h0X.comp measurable_neg measurable_id) hindep (fun _ => (√2)⁻¹) (fun _ => (√2)⁻¹) μ
    (fun _ => by positivity) S (fun _ _ => by positivity) hlaw

/-- The one-sided z-test p-value of a comparison with the control is measurable. -/
lemma measurable_manyToOne {X₀ Xj : Ω → ℝ} (h0 : Measurable X₀) (hj : Measurable Xj) (m : ℝ) :
    Measurable fun ω => 1 - cdf (gaussianReal 0 1) ((Xj ω - X₀ ω) / √2 + m) :=
  measurable_one_sub_cdf_gaussian.comp (((hj.sub h0).div_const _).add measurable_const)

/-- Validity of a null p-value in the comparison with a control. -/
lemma isValidPValue_manyToOne (P : Measure Ω) {X₀ Xi : Ω → ℝ} (h0 : Measurable X₀)
    (hi : Measurable Xi) (h0i : IndepFun X₀ Xi P) (hlaw0 : P.map X₀ = gaussianReal 0 1)
    (hlawi : P.map Xi = gaussianReal 0 1) {m : ℝ} (hm : m = 0) :
    IsValidPValue P fun ω => 1 - cdf (gaussianReal 0 1) ((Xi ω - X₀ ω) / √2 + m) := by
  subst hm
  have hfun : (fun ω => 1 - cdf (gaussianReal 0 1) ((Xi ω - X₀ ω) / √2 + 0))
      = fun ω => 1 - cdf (gaussianReal 0 1) ((√2)⁻¹ * (-X₀ ω) + (√2)⁻¹ * Xi ω) := by
    funext ω; rw [manyToOne_eq, add_zero]
  rw [hfun]
  exact isValidPValue_oneFactor_zTest P _ Xi h0.neg hi (h0i.comp measurable_neg measurable_id)
    (map_neg_gaussian P h0 hlaw0) hlawi inv_sqrt_two_sq_add_sq

/-- **Benjamini–Hochberg for one-sided many-to-one comparisons with a shared control.** Let
`X₀, X j` be measurable, `X₀` independent of the mutually independent `X j`, `X₀` standard
normal, and let `Z j = (X j - X₀) / √2 + μ j`. If `X i` is standard normal and `μ i = 0` for
every true null `i`, the Benjamini–Hochberg procedure applied to `1 - Φ (Z j)` at level
`α ≥ 0` has false discovery rate at most `α m₀ / m`. -/
theorem fdr_bhReject_le_manyToOne (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (μ : ι → ℝ) (H₀ : Finset ι)
    (hlaw : ∀ i ∈ H₀, P.map (X i) = gaussianReal 0 1) (hμ : ∀ i ∈ H₀, μ i = 0)
    {α : ℝ} (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j =>
        1 - cdf (gaussianReal 0 1) ((X j ω - X₀ ω) / √2 + μ j))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) :=
  fdr_bhReject_le_of_prds P hα _ (fun j => measurable_manyToOne h0 (hX j) _) H₀
    (fun i hi => isValidPValue_manyToOne P h0 (hX i)
      (h0X.comp measurable_id (measurable_pi_apply i)) hlaw0 (hlaw i hi) (hμ i hi))
    (isPRDSOn_manyToOne P X₀ X h0 hX h0X hindep μ H₀ hlaw)

/-- **Hochberg's procedure for one-sided many-to-one comparisons with a shared control**
controls the family-wise error rate at level `α`, under the hypotheses of
`fdr_bhReject_le_manyToOne`. -/
theorem fwer_hochberg_le_manyToOne (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (μ : ι → ℝ) (H₀ : Finset ι)
    (hlaw : ∀ i ∈ H₀, P.map (X i) = gaussianReal 0 1) (hμ : ∀ i ∈ H₀, μ i = 0)
    {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hochberg α fun j ω =>
        1 - cdf (gaussianReal 0 1) ((X j ω - X₀ ω) / √2 + μ j))
      ≤ ENNReal.ofReal α :=
  fwer_hochberg_le_of_prds P hα _ (fun j => measurable_manyToOne h0 (hX j) _) H₀
    (fun i hi => isValidPValue_manyToOne P h0 (hX i)
      (h0X.comp measurable_id (measurable_pi_apply i)) hlaw0 (hlaw i hi) (hμ i hi))
    (isPRDSOn_manyToOne_restrict P X₀ X h0 hX h0X hindep μ H₀ hlaw)

/-- **Hommel's procedure for one-sided many-to-one comparisons with a shared control**
controls the family-wise error rate at level `α`, under the hypotheses of
`fdr_bhReject_le_manyToOne`. -/
theorem fwer_hommel_le_manyToOne (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → ℝ)
    (X : ι → Ω → ℝ) (h0 : Measurable X₀) (hX : ∀ j, Measurable (X j))
    (h0X : IndepFun X₀ (fun ω j => X j ω) P) (hindep : iIndepFun X P)
    (hlaw0 : P.map X₀ = gaussianReal 0 1) (μ : ι → ℝ) (H₀ : Finset ι)
    (hlaw : ∀ i ∈ H₀, P.map (X i) = gaussianReal 0 1) (hμ : ∀ i ∈ H₀, μ i = 0)
    {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hommel α fun j ω =>
        1 - cdf (gaussianReal 0 1) ((X j ω - X₀ ω) / √2 + μ j))
      ≤ ENNReal.ofReal α :=
  fwer_hommel_le_of_prds P hα _ (fun j => measurable_manyToOne h0 (hX j) _) H₀
    (fun i hi => isValidPValue_manyToOne P h0 (hX i)
      (h0X.comp measurable_id (measurable_pi_apply i)) hlaw0 (hlaw i hi) (hμ i hi))
    (isPRDSOn_manyToOne_restrict P X₀ X h0 hX h0X hindep μ H₀ hlaw)

/-- In the comparison with a control, two statistics `(X₁ - X₀) / √2` and `(X₂ - X₀) / √2` have
covariance `1 / 2`, when `X₀, X₁, X₂` are pairwise independent, square-integrable and
`Var X₀ = 1`. -/
theorem covariance_manyToOne (P : Measure Ω) [IsProbabilityMeasure P] (X₀ X₁ X₂ : Ω → ℝ)
    (h0 : MemLp X₀ 2 P) (h1 : MemLp X₁ 2 P) (h2 : MemLp X₂ 2 P)
    (h01 : IndepFun X₀ X₁ P) (h02 : IndepFun X₀ X₂ P) (h12 : IndepFun X₁ X₂ P)
    (hvar : Var[X₀; P] = 1) :
    cov[fun ω => (X₁ ω - X₀ ω) / √2, fun ω => (X₂ ω - X₀ ω) / √2; P] = 1 / 2 := by
  have hf : ∀ X : Ω → ℝ, (fun ω => (X ω - X₀ ω) / √2)
      = fun ω => (√2)⁻¹ * (-X₀ ω) + (√2)⁻¹ * X ω := fun X => by
    funext ω; have := manyToOne_eq (X₀ ω) (X ω) 0; simpa using this
  rw [hf X₁, hf X₂, covariance_oneFactor P (fun ω => -X₀ ω) X₁ X₂ h0.neg h1 h2
    (h01.comp measurable_neg measurable_id) (h02.comp measurable_neg measurable_id) h12
    (by rw [variance_fun_neg, hvar])]
  rw [← sq, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

end ManyToOne

end Applied.MultipleTesting
