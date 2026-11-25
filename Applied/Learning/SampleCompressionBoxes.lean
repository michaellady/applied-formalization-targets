import Applied.Learning.SampleCompression

/-!
# Intervals and axis-parallel rectangles: compression schemes of size two and four

All results are for the definitions of `Applied.Learning.SampleCompression` (finite domain,
labelled schemes without side information).

* `intervalClass X`: on a finite linear order `X`, the functions `x ↦ (a ≤ x ∧ x ≤ b)` for
  `a, b : X`, together with the constant `false` function.
  `CompressionScheme.interval`: a scheme of size `2` (keep a smallest and a largest positive
  example, predict `true` between them); `vcDim_intervalClass_le_two`.
* `rectClass A B`: on the finite grid `A × B` of two finite linear orders, the indicator
  functions of the rectangles `[a₁, b₁] × [a₂, b₂]`, together with the constant `false`
  function. `CompressionScheme.rect`: a scheme of size `4` (keep positive examples with
  smallest and largest first and second coordinate, predict `true` on their bounding box);
  `vcDim_rectClass_le_four`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace Applied.Learning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Keeping an extreme positive example -/

section Extreme

variable {α : Type*} [LinearOrder α]

/-- The positively labelled examples of `S`. -/
def positives (S : Finset (X × Bool)) : Finset (X × Bool) := S.filter (fun e => e.2 = true)

/-- A positive example of `S` minimising `f` (nothing if `S` has no positive example). -/
noncomputable def keepMin (f : X → α) (S : Finset (X × Bool)) : Finset (X × Bool) :=
  if h : (positives S).Nonempty then {(exists_min_image _ (fun e => f e.1) h).choose} else ∅

/-- A positive example of `S` maximising `f` (nothing if `S` has no positive example). -/
noncomputable def keepMax (f : X → α) (S : Finset (X × Bool)) : Finset (X × Bool) :=
  if h : (positives S).Nonempty then {(exists_max_image _ (fun e => f e.1) h).choose} else ∅

lemma mem_keepMin {f : X → α} {S : Finset (X × Bool)} {e : X × Bool} (he : e ∈ keepMin f S) :
    e ∈ S ∧ e.2 = true := by
  unfold keepMin at he
  split_ifs at he with h
  · rw [mem_singleton.1 he]
    exact mem_filter.1 (exists_min_image _ (fun e => f e.1) h).choose_spec.1
  · simp at he

lemma mem_keepMax {f : X → α} {S : Finset (X × Bool)} {e : X × Bool} (he : e ∈ keepMax f S) :
    e ∈ S ∧ e.2 = true := by
  unfold keepMax at he
  split_ifs at he with h
  · rw [mem_singleton.1 he]
    exact mem_filter.1 (exists_max_image _ (fun e => f e.1) h).choose_spec.1
  · simp at he

lemma card_keepMin_le (f : X → α) (S : Finset (X × Bool)) : (keepMin f S).card ≤ 1 := by
  unfold keepMin; split_ifs <;> simp

lemma card_keepMax_le (f : X → α) (S : Finset (X × Bool)) : (keepMax f S).card ≤ 1 := by
  unfold keepMax; split_ifs <;> simp

lemma exists_keepMin_le {f : X → α} {S : Finset (X × Bool)} {y : X} (hy : (y, true) ∈ S) :
    ∃ e ∈ keepMin f S, e.2 = true ∧ f e.1 ≤ f y := by
  have hpos : (y, true) ∈ positives S := mem_filter.2 ⟨hy, rfl⟩
  have h : (positives S).Nonempty := ⟨_, hpos⟩
  have hs := (exists_min_image _ (fun e => f e.1) h).choose_spec
  refine ⟨_, ?_, (mem_filter.1 hs.1).2, hs.2 _ hpos⟩
  unfold keepMin
  rw [dite_eq_left h]
  exact mem_singleton_self _

lemma exists_le_keepMax {f : X → α} {S : Finset (X × Bool)} {y : X} (hy : (y, true) ∈ S) :
    ∃ e ∈ keepMax f S, e.2 = true ∧ f y ≤ f e.1 := by
  have hpos : (y, true) ∈ positives S := mem_filter.2 ⟨hy, rfl⟩
  have h : (positives S).Nonempty := ⟨_, hpos⟩
  have hs := (exists_max_image _ (fun e => f e.1) h).choose_spec
  refine ⟨_, ?_, (mem_filter.1 hs.1).2, hs.2 _ hpos⟩
  unfold keepMax
  rw [dite_eq_left h]
  exact mem_singleton_self _

/-- A finite set of more than `k` points, from which at most `k` points have been chosen, has a
point that was not chosen. (This is Mathlib's `Finset.exists_mem_notMem_of_card_lt_card`; the
local name is kept for the two uses below.) -/
lemma exists_mem_notMem_of_card_lt {A U : Finset X} (h : U.card < A.card) :
    ∃ y ∈ A, y ∉ U :=
  Finset.exists_mem_notMem_of_card_lt_card h

end Extreme

/-! ### Intervals on a finite linear order -/

section Interval

variable (X) in
/-- Intervals `[a, b]` on a finite linear order, together with the constant `false` function. -/
def intervalClass [LinearOrder X] : Finset (X → Bool) :=
  insert (fun _ => false) (univ.image (fun p : X × X => fun x => decide (p.1 ≤ x ∧ x ≤ p.2)))

variable [LinearOrder X]

/-- Concepts of `intervalClass` are convex. -/
lemma intervalClass_convex {c : X → Bool} (hc : c ∈ intervalClass X) {u w y : X}
    (hu : c u = true) (hw : c w = true) (huy : u ≤ y) (hyw : y ≤ w) : c y = true := by
  rcases mem_insert.1 hc with rfl | hc
  · simp at hu
  · obtain ⟨p, -, rfl⟩ := mem_image.1 hc
    simp only [decide_eq_true_eq] at hu hw ⊢
    exact ⟨hu.1.trans huy, hyw.trans hw.2⟩

/-- Keep a smallest and a largest positive example. -/
noncomputable def intervalCompress (S : Finset (X × Bool)) : Finset (X × Bool) :=
  keepMin id S ∪ keepMax id S

/-- Predict `true` between some kept positive example and some kept positive example. -/
def intervalReconstruct (T : Finset (X × Bool)) (y : X) : Bool :=
  decide ((∃ e ∈ T, e.2 = true ∧ e.1 ≤ y) ∧ (∃ e ∈ T, e.2 = true ∧ y ≤ e.1))

lemma mem_intervalCompress {S : Finset (X × Bool)} {e : X × Bool}
    (he : e ∈ intervalCompress S) : e ∈ S ∧ e.2 = true := by
  rcases mem_union.1 he with h | h
  · exact mem_keepMin h
  · exact mem_keepMax h

/-- **Intervals have a compression scheme of size `2`:** keep a smallest and a largest positive
example (nothing if there is none) and predict `true` between them. -/
noncomputable def CompressionScheme.interval : CompressionScheme (intervalClass X) 2 where
  compress := intervalCompress
  reconstruct := intervalReconstruct
  compress_subset _ _ _ he := (mem_intervalCompress he).1
  card_compress_le S _ :=
    (card_union_le _ _).trans (add_le_add (card_keepMin_le _ _) (card_keepMax_le _ _))
  consistent S hS e he := by
    obtain ⟨c, hc, hcS⟩ := hS
    rcases e with ⟨y, b⟩
    unfold intervalReconstruct
    cases b
    · simp only [decide_eq_false_iff_not, not_and]
      rintro ⟨u, hu, -, huy⟩ ⟨w, hw, -, hyw⟩
      obtain ⟨huS, hu2⟩ := mem_intervalCompress hu
      obtain ⟨hwS, hw2⟩ := mem_intervalCompress hw
      have := intervalClass_convex hc ((hcS _ huS).trans hu2) ((hcS _ hwS).trans hw2) huy hyw
      rw [hcS _ he] at this
      exact absurd this (by simp)
    · obtain ⟨u, hu, hu2, huy⟩ := exists_keepMin_le (f := id) he
      obtain ⟨w, hw, hw2, hyw⟩ := exists_le_keepMax (f := id) he
      simp only [decide_eq_true_eq]
      exact ⟨⟨u, mem_union_left _ hu, hu2, huy⟩, ⟨w, mem_union_right _ hw, hw2, hyw⟩⟩

/-- The class of intervals has VC dimension at most `2`. -/
lemma vcDim_intervalClass_le_two : vcDim (intervalClass X) ≤ 2 := by
  refine vcDim_le_iff.2 fun A hsh => ?_
  by_contra hcon
  push Not at hcon
  have hne : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨u, hu, hmin⟩ := exists_min_image A id hne
  obtain ⟨w, hw, hmax⟩ := exists_max_image A id hne
  obtain ⟨y, hy, hyU⟩ := exists_mem_notMem_of_card_lt (A := A) (U := {u, w})
    ((card_le_two).trans_lt hcon)
  obtain ⟨c, hc, hcA⟩ := hsh (fun x => decide (x ≠ y))
  have hyu : u ≠ y := fun h => hyU (by simp [h])
  have hyw : w ≠ y := fun h => hyU (by simp [h])
  have h1 : c u = true := by rw [hcA u hu]; simp [hyu]
  have h2 : c w = true := by rw [hcA w hw]; simp [hyw]
  have h3 : c y = false := by rw [hcA y hy]; simp
  rw [intervalClass_convex (y := y) hc h1 h2 (hmin y hy) (hmax y hy)] at h3
  exact absurd h3 (by simp)

end Interval

/-! ### Axis-parallel rectangles in a finite grid -/

section Rect

variable {A B : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
  [Fintype B] [DecidableEq B] [LinearOrder B]

variable (A B) in
/-- Axis-parallel rectangles `[a₁, b₁] × [a₂, b₂]` in the grid `A × B`, together with the
constant `false` function. -/
def rectClass : Finset (A × B → Bool) :=
  insert (fun _ => false) (univ.image (fun p : (A × A) × (B × B) => fun z =>
    decide ((p.1.1 ≤ z.1 ∧ z.1 ≤ p.1.2) ∧ (p.2.1 ≤ z.2 ∧ z.2 ≤ p.2.2))))

/-- Concepts of `rectClass` contain the bounding box of any four of their points. -/
lemma rectClass_convex {c : A × B → Bool} (hc : c ∈ rectClass A B) {u₁ u₂ v₁ v₂ z : A × B}
    (hu₁ : c u₁ = true) (hu₂ : c u₂ = true) (hv₁ : c v₁ = true) (hv₂ : c v₂ = true)
    (h₁ : u₁.1 ≤ z.1) (h₂ : z.1 ≤ u₂.1) (h₃ : v₁.2 ≤ z.2) (h₄ : z.2 ≤ v₂.2) : c z = true := by
  rcases mem_insert.1 hc with rfl | hc
  · simp at hu₁
  · obtain ⟨p, -, rfl⟩ := mem_image.1 hc
    simp only [decide_eq_true_eq] at hu₁ hu₂ hv₁ hv₂ ⊢
    exact ⟨⟨hu₁.1.1.trans h₁, h₂.trans hu₂.1.2⟩, ⟨hv₁.2.1.trans h₃, h₄.trans hv₂.2.2⟩⟩

/-- Keep positive examples with smallest and largest first and second coordinate. -/
noncomputable def rectCompress (S : Finset ((A × B) × Bool)) : Finset ((A × B) × Bool) :=
  keepMin Prod.fst S ∪ keepMax Prod.fst S ∪ keepMin Prod.snd S ∪ keepMax Prod.snd S

/-- Predict `true` on the bounding box of the kept positive examples. -/
def rectReconstruct (T : Finset ((A × B) × Bool)) (z : A × B) : Bool :=
  decide (((∃ e ∈ T, e.2 = true ∧ e.1.1 ≤ z.1) ∧ (∃ e ∈ T, e.2 = true ∧ z.1 ≤ e.1.1)) ∧
    ((∃ e ∈ T, e.2 = true ∧ e.1.2 ≤ z.2) ∧ (∃ e ∈ T, e.2 = true ∧ z.2 ≤ e.1.2)))

lemma mem_rectCompress {S : Finset ((A × B) × Bool)} {e : (A × B) × Bool}
    (he : e ∈ rectCompress S) : e ∈ S ∧ e.2 = true := by
  simp only [rectCompress, mem_union] at he
  rcases he with ((h | h) | h) | h
  · exact mem_keepMin h
  · exact mem_keepMax h
  · exact mem_keepMin h
  · exact mem_keepMax h

/-- **Axis-parallel rectangles have a compression scheme of size `4`:** keep positive examples
with smallest and largest first and second coordinate (nothing if there is no positive
example) and predict `true` on their bounding box. -/
noncomputable def CompressionScheme.rect : CompressionScheme (rectClass A B) 4 where
  compress := rectCompress
  reconstruct := rectReconstruct
  compress_subset _ _ _ he := (mem_rectCompress he).1
  card_compress_le S _ := by
    unfold rectCompress
    have := card_union_le (keepMin Prod.fst S ∪ keepMax Prod.fst S ∪ keepMin Prod.snd S)
      (keepMax Prod.snd S)
    have := card_union_le (keepMin Prod.fst S ∪ keepMax Prod.fst S) (keepMin Prod.snd S)
    have := card_union_le (keepMin Prod.fst S) (keepMax Prod.fst S)
    have := card_keepMin_le Prod.fst S
    have := card_keepMax_le Prod.fst S
    have := card_keepMin_le Prod.snd S
    have := card_keepMax_le Prod.snd S
    omega
  consistent S hS e he := by
    obtain ⟨c, hc, hcS⟩ := hS
    rcases e with ⟨z, b⟩
    unfold rectReconstruct
    have pos : ∀ e ∈ rectCompress S, c e.1 = true := fun e h =>
      (hcS _ (mem_rectCompress h).1).trans (mem_rectCompress h).2
    cases b
    · simp only [decide_eq_false_iff_not]
      rintro ⟨⟨⟨u₁, hu₁, -, h₁⟩, ⟨u₂, hu₂, -, h₂⟩⟩, ⟨⟨v₁, hv₁, -, h₃⟩, ⟨v₂, hv₂, -, h₄⟩⟩⟩
      have := rectClass_convex hc (pos _ hu₁) (pos _ hu₂) (pos _ hv₁) (pos _ hv₂) h₁ h₂ h₃ h₄
      rw [hcS _ he] at this
      exact absurd this (by simp)
    · obtain ⟨u₁, hu₁, hu₁', h₁⟩ := exists_keepMin_le (f := Prod.fst) he
      obtain ⟨u₂, hu₂, hu₂', h₂⟩ := exists_le_keepMax (f := Prod.fst) he
      obtain ⟨v₁, hv₁, hv₁', h₃⟩ := exists_keepMin_le (f := Prod.snd) he
      obtain ⟨v₂, hv₂, hv₂', h₄⟩ := exists_le_keepMax (f := Prod.snd) he
      apply decide_eq_true
      exact ⟨⟨⟨u₁, by simp [rectCompress, hu₁], hu₁', h₁⟩,
        ⟨u₂, by simp [rectCompress, hu₂], hu₂', h₂⟩⟩,
        ⟨⟨v₁, by simp [rectCompress, hv₁], hv₁', h₃⟩, ⟨v₂, by simp [rectCompress, hv₂], hv₂', h₄⟩⟩⟩

/-- The class of axis-parallel rectangles has VC dimension at most `4`. -/
lemma vcDim_rectClass_le_four : vcDim (rectClass A B) ≤ 4 := by
  refine vcDim_le_iff.2 fun P hsh => ?_
  by_contra hcon
  push Not at hcon
  have hne : P.Nonempty := card_pos.1 (by omega)
  obtain ⟨u₁, hu₁, h₁⟩ := exists_min_image P Prod.fst hne
  obtain ⟨u₂, hu₂, h₂⟩ := exists_max_image P Prod.fst hne
  obtain ⟨v₁, hv₁, h₃⟩ := exists_min_image P Prod.snd hne
  obtain ⟨v₂, hv₂, h₄⟩ := exists_max_image P Prod.snd hne
  have hU : ({u₁, u₂, v₁, v₂} : Finset (A × B)).card < P.card := by
    refine lt_of_le_of_lt ?_ hcon
    refine (card_insert_le _ _).trans ?_
    refine (Nat.succ_le_succ (card_insert_le _ _)).trans ?_
    refine (Nat.succ_le_succ (Nat.succ_le_succ card_le_two)).trans ?_
    omega
  obtain ⟨y, hy, hyU⟩ := exists_mem_notMem_of_card_lt hU
  obtain ⟨c, hc, hcP⟩ := hsh (fun x => decide (x ≠ y))
  have ht : ∀ x ∈ P, x ≠ y → c x = true := fun x hx hxy => by rw [hcP x hx]; simp [hxy]
  have n₁ : u₁ ≠ y := fun h => hyU (by simp [h])
  have n₂ : u₂ ≠ y := fun h => hyU (by simp [h])
  have n₃ : v₁ ≠ y := fun h => hyU (by simp [h])
  have n₄ : v₂ ≠ y := fun h => hyU (by simp [h])
  have h5 : c y = false := by rw [hcP y hy]; simp
  rw [rectClass_convex hc (ht _ hu₁ n₁) (ht _ hu₂ n₂) (ht _ hv₁ n₃) (ht _ hv₂ n₄)
    (h₁ y hy) (h₂ y hy) (h₃ y hy) (h₄ y hy)] at h5
  exact absurd h5 (by simp)

end Rect

end Applied.Learning
