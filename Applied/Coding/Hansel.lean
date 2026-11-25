import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Hansel's lemma on covering a complete graph by complete bipartite graphs

Let `V` be a finite set of `N` vertices and let `(X i, Y i)`, `i ∈ I`, be pairs of disjoint
finite sets (the two sides of a complete bipartite graph `Bᵢ`). If every pair of distinct
vertices of `V` is an edge of some `Bᵢ` (one endpoint in `X i`, the other in `Y i`), then
`N log₂ N ≤ ∑ᵢ |V(Bᵢ) ∩ V|`, in particular `N log₂ N ≤ ∑ᵢ (|X i| + |Y i|)`.

* `BicliqueCover V I X Y`: the covering hypothesis.
* `sum_hanselWeight_le_one`: the key inequality `∑_{v ∈ V} 2^{-d(v)} ≤ 1`, where `d(v)` is the
  number of indices `i` with `v ∈ X i ∪ Y i` (written as a product weight). This is the
  probabilistic proof (delete one side of every `Bᵢ` at random; at most one vertex survives),
  carried out as an induction on `I`.
* `hansel`: `N log₂ N ≤ ∑ᵢ |{v ∈ V : v ∈ X i ∨ v ∈ Y i}|`.
* `hansel_card`: `N log₂ N ≤ ∑ᵢ (|X i| + |Y i|)`.
-/

open Finset

namespace Applied.Coding

variable {α ι : Type*} [DecidableEq α]

/-- The pairs `(X i, Y i)`, `i ∈ I`, cover all pairs of distinct vertices of `V`: for distinct
`u, v ∈ V` there is `i ∈ I` with `u ∈ X i, v ∈ Y i` or `v ∈ X i, u ∈ Y i`. -/
def BicliqueCover (V : Finset α) (I : Finset ι) (X Y : ι → Finset α) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, u ≠ v → ∃ i ∈ I, (u ∈ X i ∧ v ∈ Y i) ∨ (v ∈ X i ∧ u ∈ Y i)

/-- The weight `2^{-d(v)}` of a vertex, written as a product over `I`. -/
noncomputable def hanselWeight (I : Finset ι) (X Y : ι → Finset α) (v : α) : ℝ :=
  ∏ i ∈ I, if v ∈ X i ∨ v ∈ Y i then (1 / 2 : ℝ) else 1

theorem hanselWeight_eq (I : Finset ι) (X Y : ι → Finset α) (v : α) :
    hanselWeight I X Y v = (1 / 2 : ℝ) ^ (I.filter fun i => v ∈ X i ∨ v ∈ Y i).card := by
  classical
  rw [hanselWeight, prod_ite, prod_const, prod_const_one, mul_one]

/-- **Key inequality of Hansel's lemma**: `∑_{v ∈ V} 2^{-d(v)} ≤ 1`. -/
theorem sum_hanselWeight_le_one [DecidableEq ι] (I : Finset ι) (X Y : ι → Finset α)
    (hdisj : ∀ i ∈ I, Disjoint (X i) (Y i)) :
    ∀ V : Finset α, BicliqueCover V I X Y → ∑ v ∈ V, hanselWeight I X Y v ≤ 1 := by
  induction I using Finset.induction_on with
  | empty =>
    intro V hV
    simp only [hanselWeight, prod_empty, sum_const, nsmul_eq_mul, mul_one]
    have : V.card ≤ 1 := by
      rw [card_le_one]
      intro u hu v hv
      by_contra h
      obtain ⟨i, hi, -⟩ := hV u hu v hv h
      simp at hi
    exact_mod_cast this
  | insert j I hj ih =>
    intro V hV
    have hdisj' : ∀ i ∈ I, Disjoint (X i) (Y i) := fun i hi => hdisj i (mem_insert_of_mem hi)
    have hjd := hdisj j (mem_insert_self j I)
    have hX : BicliqueCover (V.filter (· ∉ X j)) I X Y := by
      intro u hu v hv huv
      rw [mem_filter] at hu hv
      obtain ⟨i, hi, h⟩ := hV u hu.1 v hv.1 huv
      rcases mem_insert.mp hi with rfl | hi
      · exfalso
        rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hu.2 h1
        · exact hv.2 h1
      · exact ⟨i, hi, h⟩
    have hY : BicliqueCover (V.filter (· ∉ Y j)) I X Y := by
      intro u hu v hv huv
      rw [mem_filter] at hu hv
      obtain ⟨i, hi, h⟩ := hV u hu.1 v hv.1 huv
      rcases mem_insert.mp hi with rfl | hi
      · exfalso
        rcases h with ⟨-, h1⟩ | ⟨-, h1⟩
        · exact hv.2 h1
        · exact hu.2 h1
      · exact ⟨i, hi, h⟩
    have h1 := ih hdisj' _ hX
    have h2 := ih hdisj' _ hY
    rw [sum_filter] at h1 h2
    have key : ∀ v ∈ V, hanselWeight (insert j I) X Y v =
        ((if v ∉ X j then hanselWeight I X Y v else 0) +
          (if v ∉ Y j then hanselWeight I X Y v else 0)) / 2 := by
      intro v _
      rw [hanselWeight, prod_insert hj, ← hanselWeight]
      by_cases hx : v ∈ X j
      · have hy : v ∉ Y j := disjoint_left.mp hjd hx
        simp [hx, hy]
        ring
      · by_cases hy : v ∈ Y j
        · simp [hx, hy]; ring
        · simp [hx, hy]
    rw [sum_congr rfl key, ← sum_div, sum_add_distrib, div_le_one (by norm_num)]
    linarith

/-- Double counting: `∑_{v ∈ V} d(v) = ∑_{i ∈ I} |{v ∈ V : v ∈ X i ∪ Y i}|`. -/
theorem sum_degree_eq (V : Finset α) (I : Finset ι) (X Y : ι → Finset α) :
    ∑ v ∈ V, (I.filter fun i => v ∈ X i ∨ v ∈ Y i).card =
      ∑ i ∈ I, (V.filter fun v => v ∈ X i ∨ v ∈ Y i).card := by
  classical
  simp only [card_filter]
  exact sum_comm

/-- **Hansel's lemma** (1964). If complete bipartite graphs with sides `(X i, Y i)` (disjoint)
cover all pairs of distinct vertices of a finite set `V` with `N` elements, then
`N log₂ N ≤ ∑ᵢ |{v ∈ V : v ∈ X i ∨ v ∈ Y i}|`. -/
theorem hansel [DecidableEq ι] (V : Finset α) (I : Finset ι) (X Y : ι → Finset α)
    (hdisj : ∀ i ∈ I, Disjoint (X i) (Y i)) (hcov : BicliqueCover V I X Y) :
    (V.card : ℝ) * Real.logb 2 V.card ≤
      ∑ i ∈ I, ((V.filter fun v => v ∈ X i ∨ v ∈ Y i).card : ℝ) := by
  set d : α → ℕ := fun v => (I.filter fun i => v ∈ X i ∨ v ∈ Y i).card with hd
  have hsum : (∑ i ∈ I, ((V.filter fun v => v ∈ X i ∨ v ∈ Y i).card : ℝ)) =
      ∑ v ∈ V, (d v : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, sum_degree_eq]
  rw [hsum]
  rcases V.eq_empty_or_nonempty with rfl | hne
  · simp
  have hN : (0 : ℝ) < V.card := by exact_mod_cast hne.card_pos
  have hw := sum_hanselWeight_le_one I X Y hdisj V hcov
  simp only [hanselWeight_eq] at hw
  -- Jensen for the concave logarithm with uniform weights `1/N`
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := V)
    (w := fun _ => (1 / (V.card : ℝ))) (p := fun v => (1 / 2 : ℝ) ^ d v)
    (fun _ _ => by positivity) (by rw [sum_const, nsmul_eq_mul]; field_simp)
    (fun v _ => Set.mem_Ioi.mpr (by positivity))
  simp only [smul_eq_mul] at hJ
  rw [← mul_sum] at hJ
  have hle : Real.log (1 / (V.card : ℝ) * ∑ v ∈ V, (1 / 2 : ℝ) ^ d v) ≤
      Real.log (1 / (V.card : ℝ)) := by
    apply Real.log_le_log
    · have : 0 < ∑ v ∈ V, (1 / 2 : ℝ) ^ d v := sum_pos (fun _ _ => by positivity) hne
      positivity
    · calc 1 / (V.card : ℝ) * ∑ v ∈ V, (1 / 2 : ℝ) ^ d v ≤ 1 / (V.card : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hw (by positivity)
        _ = 1 / (V.card : ℝ) := mul_one _
  have hlog : ∀ v, Real.log ((1 / 2 : ℝ) ^ d v) = -(d v * Real.log 2) := by
    intro v
    rw [Real.log_pow, one_div, Real.log_inv]
    ring
  simp only [hlog] at hJ
  rw [← mul_sum, sum_neg_distrib, ← sum_mul, one_div] at hJ
  rw [one_div, Real.log_inv] at hle
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : (V.card : ℝ) * Real.log V.card ≤ (∑ v ∈ V, (d v : ℝ)) * Real.log 2 := by
    have h3 := hJ.trans hle
    have h4 : (V.card : ℝ)⁻¹ * -((∑ v ∈ V, (d v : ℝ)) * Real.log 2) * V.card =
        -((∑ v ∈ V, (d v : ℝ)) * Real.log 2) := by field_simp
    nlinarith
  rw [Real.logb, mul_div_assoc', div_le_iff₀ hl2]
  exact key

/-- **Hansel's lemma**, plain form: `N log₂ N ≤ ∑ᵢ (|X i| + |Y i|)`. -/
theorem hansel_card [DecidableEq ι] (V : Finset α) (I : Finset ι) (X Y : ι → Finset α)
    (hdisj : ∀ i ∈ I, Disjoint (X i) (Y i)) (hcov : BicliqueCover V I X Y) :
    (V.card : ℝ) * Real.logb 2 V.card ≤ ∑ i ∈ I, (((X i).card + (Y i).card : ℕ) : ℝ) := by
  refine (hansel V I X Y hdisj hcov).trans (sum_le_sum fun i _ => ?_)
  have : (V.filter fun v => v ∈ X i ∨ v ∈ Y i) ⊆ X i ∪ Y i := by
    intro v hv
    simpa using (mem_filter.mp hv).2
  exact_mod_cast (card_le_card this).trans (card_union_le _ _)

end Applied.Coding
