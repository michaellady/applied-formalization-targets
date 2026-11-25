import Applied.Statistics.GroupSequentialCanonical
import Applied.Statistics.GroupSequentialBoundaries
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.InfinitePi

/-!
# Group-sequential designs: joint normality and boundaries for the canonical distribution

Setting of `GroupSequentialCanonical.lean`: `ξ 0, ξ 1, …` are measurable, mutually independent
and standard normal under a probability measure `P`; `S n = ξ 0 + … + ξ (n - 1)` and
`Z n = S n / √n`. Look times are natural numbers `t k`.

## Main results

Joint normality (rung 11 of the roadmap):

* `hasGaussianLaw_partialSum_vec`, `hasGaussianLaw_zStat_vec`: for any look times
  `t : Fin K → ℕ`, the vectors `(S (t k))_k` and `(Z (t k))_k` have a Gaussian law on
  `Fin K → ℝ` in Mathlib's sense (`HasGaussianLaw`, i.e. `IsGaussian` of the image measure;
  see also `isGaussian_map_zStat_vec`). Route: the first `N` increments form a Gaussian vector
  (`iIndepFun.hasGaussianLaw`), and the statistics are a linear image of it.

The law depends only on the look times:

* `canonicalMeasure`: `ℝ^ℕ` with the product of standard normal laws; `coord i` is the
  `i`-th coordinate. `canonicalZLaw t` is the law of `(Z (t k))_k` in this model.
* `map_zStat_vec_eq_canonicalZLaw`: in every model as above, the joint law of `(Z (t k))_k`
  equals `canonicalZLaw t` (index set arbitrary).
* `map_zStat_vec_eq_of_same_looks`: two models with the same look times give equal joint laws
  on `Fin K → ℝ`.
* `isGaussian_canonicalZLaw`, `covariance_canonicalZLaw`: the canonical law is Gaussian and its
  coordinates have covariance `√(t i / t j)` for `0 < t i ≤ t j`.

Boundaries computed once from the canonical distribution:

* `exists_alphaSpending_boundaries_gaussian`: for look times `t k > 0` (`k < K`) and a
  non-decreasing spending function with `s 0 = 0`, `s K ≤ 1`, there are boundaries
  `c : ℕ → EReal`, depending only on `t`, `s` and `K`, such that in *every* model as above the
  first-crossing probability at look `k < K` is exactly `s (k + 1) - s k` and the overall
  type-I error is exactly `s K - s 0`.
* `exists_common_boundary_gaussian`: for `K ≥ 1` looks and `0 ≤ α ≤ 1`, a common boundary with
  overall type-I error exactly `α` in every model (Pocock-type design).

All of this is under the null hypothesis (zero drift).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Applied.GroupSequential

section JointLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ξ : ℕ → Ω → ℝ}

/-- Partial sums as sums over `Fin N` with 0/1 coefficients. -/
lemma sum_fin_indicator_mul {N n : ℕ} (hn : n ≤ N) (c : ℝ) (f : ℕ → ℝ) :
    ∑ i : Fin N, (c * if (i : ℕ) < n then 1 else 0) * f i = c * ∑ i ∈ range n, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (c * if i < n then 1 else 0) * f i) N, Finset.mul_sum]
  have : range n = (range N).filter (· < n) := by
    ext i; simp only [mem_range, mem_filter]; omega
  rw [this, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- The vector `(ξ 0, …, ξ (N - 1))` has a Gaussian law on `Fin N → ℝ`. -/
theorem hasGaussianLaw_finVec (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, P.map (ξ i) = gaussianReal 0 1) (hindep : iIndepFun ξ P) (N : ℕ) :
    HasGaussianLaw (fun ω (i : Fin N) => ξ i ω) P :=
  iIndepFun.hasGaussianLaw (X := fun (i : Fin N) => ξ i)
    (fun i => HasLaw.hasGaussianLaw ⟨(hξ i).aemeasurable, hlaw i⟩)
    (hindep.precomp Fin.val_injective)

/-- Finitely many linear combinations of the `ξ i` are jointly Gaussian. -/
theorem hasGaussianLaw_linearCombination (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, P.map (ξ i) = gaussianReal 0 1) (hindep : iIndepFun ξ P) {K N : ℕ}
    (A : Fin K → Fin N → ℝ) :
    HasGaussianLaw (fun ω k => ∑ i : Fin N, A k i * ξ i ω) P := by
  have h := (hasGaussianLaw_finVec hξ hlaw hindep N).map_fun
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Matrix.of A)))
  convert h using 2 with ω
  funext k
  simp [Matrix.mulVec, dotProduct]

/-- **Joint normality of the partial sums.** For any look times `t : Fin K → ℕ`, the vector
`(S (t k))_k` has a Gaussian law on `Fin K → ℝ`. -/
theorem hasGaussianLaw_partialSum_vec (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, P.map (ξ i) = gaussianReal 0 1) (hindep : iIndepFun ξ P) {K : ℕ}
    (t : Fin K → ℕ) :
    HasGaussianLaw (fun ω k => partialSum ξ (t k) ω) P := by
  set N := Finset.univ.sup t
  convert hasGaussianLaw_linearCombination hξ hlaw hindep
    (fun k (i : Fin N) => 1 * if (i : ℕ) < t k then 1 else 0) using 2 with ω
  funext k
  rw [sum_fin_indicator_mul (f := fun i => ξ i ω) (Finset.le_sup (Finset.mem_univ k)), one_mul]
  rfl

/-- **Joint normality of the standardised statistics.** For any look times `t : Fin K → ℕ`,
the vector `(Z (t k))_k` has a Gaussian law on `Fin K → ℝ`. (For `t k = 0`, `Z (t k) = 0`.) -/
theorem hasGaussianLaw_zStat_vec (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, P.map (ξ i) = gaussianReal 0 1) (hindep : iIndepFun ξ P) {K : ℕ}
    (t : Fin K → ℕ) :
    HasGaussianLaw (fun ω k => zStat ξ (t k) ω) P := by
  set N := Finset.univ.sup t
  convert hasGaussianLaw_linearCombination hξ hlaw hindep
    (fun k (i : Fin N) => (√(t k : ℝ))⁻¹ * if (i : ℕ) < t k then 1 else 0) using 2 with ω
  funext k
  rw [sum_fin_indicator_mul (f := fun i => ξ i ω) (Finset.le_sup (Finset.mem_univ k)), zStat,
    partialSum,
    div_eq_inv_mul]

/-- The same statement with Mathlib's `IsGaussian` on the law. -/
theorem isGaussian_map_zStat_vec [IsProbabilityMeasure P] (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, P.map (ξ i) = gaussianReal 0 1) (hindep : iIndepFun ξ P) {K : ℕ}
    (t : Fin K → ℕ) :
    IsGaussian (P.map fun ω k => zStat ξ (t k) ω) :=
  (hasGaussianLaw_zStat_vec hξ hlaw hindep t).isGaussian_map

end JointLaw

section Canonical

/-- The coordinate process on `ℝ^ℕ`. -/
def coord (i : ℕ) (x : ℕ → ℝ) : ℝ := x i

/-- The canonical model: `ℝ^ℕ` with the product of standard normal laws. -/
noncomputable def canonicalMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

instance : IsProbabilityMeasure canonicalMeasure := by
  unfold canonicalMeasure; infer_instance

lemma measurable_coord (i : ℕ) : Measurable (coord i) := measurable_pi_apply i

lemma map_coord (i : ℕ) : canonicalMeasure.map (coord i) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ i

lemma iIndepFun_coord : iIndepFun coord canonicalMeasure := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map measurable_coord]
  simp only [map_coord]
  exact Measure.map_id

lemma measurable_zStat {ξ' : ℕ → (ℕ → ℝ) → ℝ} (hξ : ∀ i, Measurable (ξ' i)) (n : ℕ) :
    Measurable (zStat ξ' n) :=
  (measurable_partialSum hξ n).div_const _

/-- The canonical joint law of `(Z (t k))_k`: its law in the coordinate model. -/
noncomputable def canonicalZLaw {ι : Type*} (t : ι → ℕ) : Measure (ι → ℝ) :=
  canonicalMeasure.map fun x k => zStat coord (t k) x

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ξ : ℕ → Ω → ℝ}

/-- The law of the whole sequence `(ξ i)_i` is the canonical product measure. -/
theorem map_seq_eq_canonicalMeasure [IsProbabilityMeasure P] (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, P.map (ξ i) = gaussianReal 0 1) (hindep : iIndepFun ξ P) :
    P.map (fun ω i => ξ i ω) = canonicalMeasure := by
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map hξ).1 hindep]
  simp only [hlaw]
  rfl

/-- Events defined from the sequence `(ξ i)_i` have the same probability as in the canonical
model. -/
theorem measure_preimage_seq [IsProbabilityMeasure P] (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, P.map (ξ i) = gaussianReal 0 1) (hindep : iIndepFun ξ P)
    {E : Set (ℕ → ℝ)} (hE : MeasurableSet E) :
    P ((fun ω i => ξ i ω) ⁻¹' E) = canonicalMeasure E := by
  rw [← map_seq_eq_canonicalMeasure hξ hlaw hindep, Measure.map_apply (Measurable.of_eval hξ) hE]

/-- **The joint law of the interim statistics is the canonical one.** In every model with
independent standard normal `ξ i`, the law of `(Z (t k))_k` is `canonicalZLaw t`. -/
theorem map_zStat_vec_eq_canonicalZLaw [IsProbabilityMeasure P] (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, P.map (ξ i) = gaussianReal 0 1) (hindep : iIndepFun ξ P) {ι : Type*}
    (t : ι → ℕ) :
    P.map (fun ω k => zStat ξ (t k) ω) = canonicalZLaw t := by
  rw [canonicalZLaw, ← map_seq_eq_canonicalMeasure hξ hlaw hindep,
    Measure.map_map (Measurable.of_eval fun k => measurable_zStat measurable_coord (t k))
      (Measurable.of_eval hξ)]
  rfl

/-- **The law of the interim statistics depends only on the look times.** Two models with
independent standard normal increments and the same look times give the same joint law of
`(Z (t k))_{k < K}` on `Fin K → ℝ`. -/
theorem map_zStat_vec_eq_of_same_looks [IsProbabilityMeasure P] (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, P.map (ξ i) = gaussianReal 0 1) (hindep : iIndepFun ξ P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {η : ℕ → Ω' → ℝ} (hη : ∀ i, Measurable (η i))
    (hlawη : ∀ i, Q.map (η i) = gaussianReal 0 1) (hindepη : iIndepFun η Q) {K : ℕ}
    (t : Fin K → ℕ) :
    P.map (fun ω k => zStat ξ (t k) ω) = Q.map (fun ω k => zStat η (t k) ω) := by
  rw [map_zStat_vec_eq_canonicalZLaw hξ hlaw hindep, map_zStat_vec_eq_canonicalZLaw hη hlawη hindepη]

/-- The canonical joint law of `(Z (t k))_{k < K}` is Gaussian on `Fin K → ℝ`. -/
theorem isGaussian_canonicalZLaw {K : ℕ} (t : Fin K → ℕ) : IsGaussian (canonicalZLaw t) :=
  isGaussian_map_zStat_vec measurable_coord map_coord iIndepFun_coord t

/-- Covariances of the coordinates under the canonical law: `√(t i / t j)` for
`0 < t i ≤ t j`. -/
theorem covariance_canonicalZLaw {ι : Type*} (t : ι → ℕ) {i j : ι} (hi : 0 < t i)
    (hij : t i ≤ t j) :
    cov[fun x => x i, fun x => x j; canonicalZLaw t] = √((t i : ℝ) / t j) := by
  rw [canonicalZLaw, covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable
    (Measurable.of_eval fun k => measurable_zStat measurable_coord (t k)).aemeasurable]
  exact covariance_zStat_of_gaussian measurable_coord map_coord iIndepFun_coord hi hij

/-- In the canonical model `Z n` has no atoms for `n > 0`. -/
lemma canonical_zStat_atom {n : ℕ} (hn : 0 < n) (y : ℝ) :
    canonicalMeasure {x | zStat coord n x = y} = 0 := by
  have h := map_zStat measurable_coord map_coord iIndepFun_coord hn
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hm := Measure.map_apply (μ := canonicalMeasure) (measurable_zStat measurable_coord n)
    (measurableSet_singleton y)
  rw [h, measure_singleton] at hm
  exact hm.symm

end Canonical

section GaussianBoundaries

universe u

/-- **Exact alpha-spending boundaries for the canonical joint distribution.** For look times
with `t k > 0` for `k < K` and a non-decreasing spending function with `s 0 = 0` and `s K ≤ 1`,
there are boundaries `c : ℕ → EReal`, depending only on `K`, `t` and `s`, such that in every
model with independent standard normal increments the probability of first crossing at look
`k < K` is exactly `s (k + 1) - s k`, and the probability of crossing at some look is exactly
`s K - s 0`. -/
theorem exists_alphaSpending_boundaries_gaussian (K : ℕ) (t : ℕ → ℕ) (ht : ∀ k < K, 0 < t k)
    (s : ℕ → ℝ) (hs : Monotone s) (hs0 : s 0 = 0) (hsK : s K ≤ 1) :
    ∃ c : ℕ → EReal, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ξ : ℕ → Ω → ℝ), (∀ i, Measurable (ξ i)) → (∀ i, P.map (ξ i) = gaussianReal 0 1) →
      iIndepFun ξ P →
      (∀ k < K, P (firstCrossing (crossing c fun k => zStat ξ (t k)) k) =
        ENNReal.ofReal (s (k + 1) - s k)) ∧
      P (⋃ k ∈ range K, crossing c (fun k => zStat ξ (t k)) k) = ENNReal.ofReal (s K - s 0) := by
  obtain ⟨c, hc⟩ := exists_alphaSpending_boundaries canonicalMeasure
    (X := fun k => zStat coord (t k)) (fun k => measurable_zStat measurable_coord (t k)) K
    (fun k hk y => canonical_zStat_atom (ht k hk) y) s hs hs0 hsK
  refine ⟨c, fun {Ω} _ P _ ξ hξ hlaw hindep => ?_⟩
  have hX : ∀ k, Measurable (zStat ξ (t k)) := fun k =>
    (measurable_partialSum hξ (t k)).div_const _
  have hfc : ∀ k < K, P (firstCrossing (crossing c fun k => zStat ξ (t k)) k) =
      ENNReal.ofReal (s (k + 1) - s k) := by
    intro k hk
    rw [← hc k hk]
    have hE : MeasurableSet (firstCrossing (crossing c fun k => zStat coord (t k)) k) :=
      (measurableSet_crossing c (fun k => measurable_zStat measurable_coord (t k)) k).diff
        (Finset.measurableSet_biUnion _ fun j _ =>
          measurableSet_crossing c (fun k => measurable_zStat measurable_coord (t k)) j)
    convert measure_preimage_seq hξ hlaw hindep hE using 2
    ext ω
    simp [firstCrossing, crossing, zStat, partialSum, coord]
  exact ⟨hfc, measure_biUnion_eq_of_alphaSpending P (measurableSet_crossing c hX) K s hs hfc⟩

/-- **Common (Pocock-type) boundary for the canonical joint distribution.** For `K ≥ 1` looks
with `t k > 0` and `0 ≤ α ≤ 1`, there is one boundary `c`, depending only on `K`, `t` and `α`,
such that in every model with independent standard normal increments the probability that
`Z (t k) ≥ c` at some look `k < K` is exactly `α`. -/
theorem exists_common_boundary_gaussian {K : ℕ} (hK : 0 < K) (t : ℕ → ℕ)
    (ht : ∀ k < K, 0 < t k) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ c : EReal, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ξ : ℕ → Ω → ℝ), (∀ i, Measurable (ξ i)) → (∀ i, P.map (ξ i) = gaussianReal 0 1) →
      iIndepFun ξ P →
      P (⋃ k ∈ range K, {ω | c ≤ (zStat ξ (t k) ω : EReal)}) = ENNReal.ofReal α := by
  obtain ⟨c, hc⟩ := exists_common_boundary canonicalMeasure
    (X := fun k => zStat coord (t k)) (fun k => measurable_zStat measurable_coord (t k)) hK
    (fun k hk y => canonical_zStat_atom (ht k hk) y) hα0 hα1
  refine ⟨c, fun {Ω} _ P _ ξ hξ hlaw hindep => ?_⟩
  rw [← hc]
  convert measure_preimage_seq hξ hlaw hindep (Finset.measurableSet_biUnion (range K) fun j _ =>
    measurableSet_crossing (fun _ => c) (fun k => measurable_zStat measurable_coord (t k)) j)
    using 2
  · ext ω
    simp [crossing, zStat, partialSum, coord]
  · rfl

end GaussianBoundaries

end Applied.GroupSequential
