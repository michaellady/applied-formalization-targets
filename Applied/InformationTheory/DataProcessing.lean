import Applied.InformationTheory.Channel

/-!
# The log-sum inequality and the data-processing inequality

All logarithms are natural.

* `log_sum_inequality`: `(∑ a i) log ((∑ a i) / (∑ b i)) ≤ ∑ a i log (a i / b i)`.
* `postprocess P V`: the joint mass function of `(X, Z)` when `(X, Y)` has joint mass function
  `P` and `Z` is obtained from `Y` through the channel `V`.
* `mutualInfo_postprocess_le`: the **data-processing inequality** `I(X; Z) ≤ I(X; Y)`.
* `comp W V`: the cascade of two channels; `isChannel_comp`.
* `mutualInfo_joint_comp_le`, `capacity_comp_le`: cascading a second channel after `W` does not
  increase mutual information, nor capacity.
-/

open Finset Real

namespace Applied.InformationTheory

/-- **Log-sum inequality.** For nonnegative `a`, `b` on a finite set with `a i = 0` wherever
`b i = 0`, `(∑ a i) log ((∑ a i) / (∑ b i)) ≤ ∑ a i log (a i / b i)`. -/
theorem log_sum_inequality {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hac : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ ∑ i ∈ s, a i * log (a i / b i) := by
  set A := ∑ i ∈ s, a i with hA
  set B := ∑ i ∈ s, b i with hB
  by_cases hA0 : A = 0
  · have hz : ∀ i ∈ s, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).mp hA0
    rw [hA0, zero_mul, Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul]]
  have hB0 : B ≠ 0 := fun h => hA0 <| Finset.sum_eq_zero fun i hi =>
    hac i hi ((Finset.sum_eq_zero_iff_of_nonneg hb).mp h i hi)
  have hApos : 0 < A := lt_of_le_of_ne (Finset.sum_nonneg ha) (Ne.symm hA0)
  have hBpos : 0 < B := lt_of_le_of_ne (Finset.sum_nonneg hb) (Ne.symm hB0)
  have hAB : A / B ≠ 0 := div_ne_zero hA0 hB0
  have h := sum_sub_sum_le_sum_mul_log_div s a (fun i => b i * (A / B)) ha
    (fun i hi => mul_nonneg (hb i hi) (div_pos hApos hBpos).le)
    (fun i hi h0 => hac i hi ((mul_eq_zero.mp h0).resolve_right hAB))
  have hq : ∑ i ∈ s, b i * (A / B) = A := by
    rw [← Finset.sum_mul, ← hB, mul_div_cancel₀ _ hB0]
  have hterm : ∀ i ∈ s, a i * log (a i / (b i * (A / B)))
      = a i * log (a i / b i) - a i * log (A / B) := by
    intro i hi
    by_cases h0 : a i = 0
    · simp [h0]
    · have hbi : b i ≠ 0 := fun h => h0 (hac i hi h)
      rw [← div_div, log_div (div_ne_zero h0 hbi) hAB]; ring
  rw [hq, ← hA, sub_self, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← hA] at h
  linarith

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- The joint mass function of `(X, Z)` when `(X, Y)` has joint mass function `P` and `Z` is
obtained from `Y` alone through the channel `V` (so that `X → Y → Z` is a Markov chain). -/
def postprocess (P : X → Y → ℝ) (V : Y → Z → ℝ) (x : X) (z : Z) : ℝ := ∑ y, P x y * V y z

omit [Fintype X] in
lemma marginalFst_postprocess (P : X → Y → ℝ) {V : Y → Z → ℝ} (hV : IsChannel V) :
    marginalFst (postprocess P V) = marginalFst P := by
  funext x
  simp only [marginalFst, postprocess]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, hV.sum_eq_one]

omit [Fintype Z] in
lemma marginalSnd_postprocess (P : X → Y → ℝ) (V : Y → Z → ℝ) (z : Z) :
    marginalSnd (postprocess P V) z = ∑ y, marginalSnd P y * V y z := by
  simp only [marginalSnd, postprocess]
  rw [Finset.sum_comm]
  simp [Finset.sum_mul]

/-- **Data-processing inequality.** If `(X, Y)` has joint mass function `P ≥ 0` and `Z` is
produced from `Y` by a channel `V`, then `I(X; Z) ≤ I(X; Y)`. -/
theorem mutualInfo_postprocess_le (P : X → Y → ℝ) (V : Y → Z → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hV : IsChannel V) : mutualInfo (postprocess P V) ≤ mutualInfo P := by
  have key : ∀ x z, postprocess P V x z
        * log (postprocess P V x z
          / (marginalFst (postprocess P V) x * marginalSnd (postprocess P V) z))
      ≤ ∑ y, V y z * (P x y * log (P x y / (marginalFst P x * marginalSnd P y))) := by
    intro x z
    have h := log_sum_inequality univ (fun y => P x y * V y z)
      (fun y => marginalFst P x * marginalSnd P y * V y z)
      (fun y _ => mul_nonneg (hP x y) (hV.nonneg y z))
      (fun y _ => mul_nonneg (mul_nonneg (marginalFst_nonneg hP x) (marginalSnd_nonneg hP y))
        (hV.nonneg y z))
      (fun y _ h0 => by
        rcases mul_eq_zero.mp h0 with h | h
        · rcases mul_eq_zero.mp h with h | h
          · rw [le_antisymm (h ▸ le_marginalFst hP x y) (hP x y), zero_mul]
          · rw [le_antisymm (h ▸ le_marginalSnd hP x y) (hP x y), zero_mul]
        · rw [h, mul_zero])
    have hb : ∑ y, marginalFst P x * marginalSnd P y * V y z
        = marginalFst (postprocess P V) x * marginalSnd (postprocess P V) z := by
      rw [marginalFst_postprocess P hV, marginalSnd_postprocess, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hb] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
    by_cases hv : V y z = 0
    · simp [hv]
    · rw [mul_div_mul_right _ _ hv]; ring
  calc mutualInfo (postprocess P V)
      ≤ ∑ x, ∑ z, ∑ y, V y z * (P x y * log (P x y / (marginalFst P x * marginalSnd P y))) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => key x z
    _ = mutualInfo P := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, hV.sum_eq_one, one_mul]

/-- The cascade of two channels: first `W`, then `V`. -/
def comp (W : X → Y → ℝ) (V : Y → Z → ℝ) (x : X) (z : Z) : ℝ := ∑ y, W x y * V y z

omit [Fintype X] in
lemma isChannel_comp {W : X → Y → ℝ} {V : Y → Z → ℝ} (hW : IsChannel W) (hV : IsChannel V) :
    IsChannel (comp W V) where
  nonneg x z := Finset.sum_nonneg fun y _ => mul_nonneg (hW.nonneg x y) (hV.nonneg y z)
  sum_eq_one x := by
    simp only [comp]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hV.sum_eq_one, hW.sum_eq_one]

omit [Fintype X] [Fintype Z] in
lemma joint_comp (p : X → ℝ) (W : X → Y → ℝ) (V : Y → Z → ℝ) :
    joint p (comp W V) = postprocess (joint p W) V := by
  funext x z
  simp [joint, comp, postprocess, Finset.mul_sum, mul_assoc]

/-- **Data-processing inequality for channels**: for every input distribution, the cascade
`W` then `V` carries at most as much information as `W` alone. -/
theorem mutualInfo_joint_comp_le (p : X → ℝ) (W : X → Y → ℝ) (V : Y → Z → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hW : IsChannel W) (hV : IsChannel V) :
    mutualInfo (joint p (comp W V)) ≤ mutualInfo (joint p W) := by
  rw [joint_comp]
  exact mutualInfo_postprocess_le _ V (joint_nonneg hp hW) hV

/-- Cascading a second channel does not increase capacity. -/
theorem capacity_comp_le {W : X → Y → ℝ} {V : Y → Z → ℝ} (hW : IsChannel W) (hV : IsChannel V) :
    capacity (comp W V) ≤ capacity W :=
  capacity_le_of_forall_le (capacity_nonneg hW) fun p hp hsum =>
    (mutualInfo_joint_comp_le p W V hp hW hV).trans (mutualInfo_joint_le_capacity hW hp hsum)

end Applied.InformationTheory
