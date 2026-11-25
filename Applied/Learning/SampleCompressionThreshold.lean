import Applied.Learning.SampleCompression

/-!
# Thresholds on a finite linear order: a compression scheme of size one

All results are for the definitions of `Applied.Learning.SampleCompression` (finite domain,
labelled schemes without side information).

* `thresholdClass X`: the functions `x ↦ (a ≤ x)` for `a : X`, together with the constant
  `false` function (the threshold "above every point").
* `vcDim_thresholdClass_le_one`: that class has VC dimension at most `1`.
* `CompressionScheme.threshold`: a scheme of size `1` (keep the smallest positive example,
  nothing if there is none; predict `true` from that point upwards).

Intervals and rectangles are in `SampleCompressionBoxes`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace Applied.Learning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Thresholds on a finite linear order: a scheme of size `1` -/

section Threshold

variable (X) in
/-- Thresholds on a finite linear order: the functions `x ↦ decide (a ≤ x)` for `a : X`,
together with the constant `false` function (the threshold "above every point"). -/
def thresholdClass [LinearOrder X] : Finset (X → Bool) :=
  insert (fun _ => false) (univ.image (fun a x => decide (a ≤ x)))

variable [LinearOrder X]

lemma lt_of_mem_thresholdClass {c : X → Bool} (hc : c ∈ thresholdClass X) {m y : X}
    (hm : c m = true) (hy : c y = false) : y < m := by
  rcases mem_insert.1 hc with rfl | hc
  · simp at hm
  · obtain ⟨a, -, rfl⟩ := mem_image.1 hc
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_le] at hm hy
    exact lt_of_lt_of_le hy hm

/-- The class of thresholds has VC dimension at most `1`. -/
lemma vcDim_thresholdClass_le_one : vcDim (thresholdClass X) ≤ 1 := by
  refine vcDim_le_iff.2 fun A hsh => ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, m, hm, hne⟩ := one_lt_card.1 hcon
  have key : ∀ u ∈ A, ∀ v ∈ A, u < v → False := by
    intro u hu v hv huv
    obtain ⟨c, hc, hcA⟩ := hsh (fun x => decide (x = u))
    have h1 : c u = true := by rw [hcA u hu]; simp
    have h2 : c v = false := by rw [hcA v hv]; simp [huv.ne']
    exact absurd (lt_of_mem_thresholdClass hc h1 h2) (not_lt.2 huv.le)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key y hy m hm hlt
  · exact key m hm y hy hlt

/-- The points of the positively labelled examples of `S`. -/
def positivePoints (S : Finset (X × Bool)) : Finset X :=
  (S.filter (fun e => e.2 = true)).image Prod.fst

lemma mem_positivePoints {S : Finset (X × Bool)} {y : X} (h : (y, true) ∈ S) :
    y ∈ positivePoints S :=
  mem_image.2 ⟨(y, true), mem_filter.2 ⟨h, rfl⟩, rfl⟩

lemma min'_positivePoints_mem {S : Finset (X × Bool)} (h : (positivePoints S).Nonempty) :
    ((positivePoints S).min' h, true) ∈ S := by
  obtain ⟨e, he, he1⟩ := mem_image.1 ((positivePoints S).min'_mem h)
  rw [mem_filter] at he
  have : e = ((positivePoints S).min' h, true) := Prod.ext he1 he.2
  rw [← this]
  exact he.1

/-- Keep the smallest positive example, if there is one. -/
def thresholdCompress (S : Finset (X × Bool)) : Finset (X × Bool) :=
  if h : (positivePoints S).Nonempty then {((positivePoints S).min' h, true)} else ∅

/-- Predict `true` exactly at or above some kept positive example. -/
def thresholdReconstruct (T : Finset (X × Bool)) (y : X) : Bool :=
  decide (∃ e ∈ T, e.2 = true ∧ e.1 ≤ y)

/-- **Thresholds have a compression scheme of size `1`:** keep the smallest positive example
(nothing if there is none) and predict `true` from that point upwards. -/
def CompressionScheme.threshold : CompressionScheme (thresholdClass X) 1 where
  compress := thresholdCompress
  reconstruct := thresholdReconstruct
  compress_subset S _ := by
    unfold thresholdCompress
    split_ifs with h
    · exact singleton_subset_iff.2 (min'_positivePoints_mem h)
    · exact empty_subset _
  card_compress_le S _ := by
    unfold thresholdCompress
    split_ifs <;> simp
  consistent S hS e he := by
    obtain ⟨c, hc, hcS⟩ := hS
    rcases e with ⟨y, b⟩
    unfold thresholdCompress thresholdReconstruct
    split_ifs with h
    · have hmS := min'_positivePoints_mem h
      cases b
      · have hlt := lt_of_mem_thresholdClass hc (hcS _ hmS) (hcS _ he)
        simp [not_le.2 hlt]
      · have : (positivePoints S).min' h ≤ y := min'_le _ _ (mem_positivePoints he)
        simp [this]
    · cases b
      · simp
      · exact absurd ⟨y, mem_positivePoints he⟩ h

end Threshold

end Applied.Learning
