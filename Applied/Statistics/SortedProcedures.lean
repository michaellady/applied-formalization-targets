import Applied.Statistics.Simes
import Applied.Statistics.BHMonotone
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Textbook (sorted) forms of Holm, Hochberg and Benjamini–Hochberg

The library defines `holm`, `hochberg` and `bhReject` without sorting the p-values. Textbooks
state them through the order statistics `p₍₁₎ ≤ … ≤ p₍ₘ₎`. This file defines the textbook rules
for hypotheses indexed by `Fin m`, relative to a permutation `σ` that sorts the p-values
(`IsSorting q σ`: `q ∘ σ` is monotone, so `σ k` is the hypothesis at 0-based position `k`), and
proves that they reject exactly what the sort-free definitions reject.

Positions are 0-based in Lean (`k : Fin m`); the textbook 1-based position is `k + 1`.

* `holmSorted α q σ`: let `holmStop` be the first 0-based position `k` with
  `q (σ k) > α / (m - k)` (or `m` if there is none); reject `σ 0, …, σ (holmStop - 1)`.
  In 1-based terms the critical constant of position `k + 1` is `α / (m - (k + 1) + 1)`.
* `hochbergSorted α q σ`: let `hochbergStop` be the largest 1-based position `k + 1` with
  `q (σ k) ≤ α / (m - (k + 1) + 1)` (or `0`); reject the first `hochbergStop` positions.
* `bhSorted α q σ`: let `bhSortedK` be the largest 1-based position `k + 1` with
  `q (σ k) ≤ α (k + 1) / m` (or `0`); reject the first `bhSortedK` positions.

Main results, for `0 ≤ α` and *every* sorting permutation (so the sorted rules do not depend on
how ties are ordered):

* `holmSorted_eq_holm`, `hochbergSorted_eq_hochberg`, `bhSorted_eq_bhReject`;
* `bhSortedK_eq_bhK` (this one holds for every real `α`);
* `isSorting_sort`: a sorting permutation exists (`Tuple.sort`).

For `α < 0` the sorted rules can depend on the order of ties and no equality is claimed.
-/

open Finset

namespace Applied.MultipleTesting

variable {m : ℕ}

/-- `σ` sorts the vector `q`: `q (σ 0) ≤ q (σ 1) ≤ …`, i.e. `σ k` is the index of the
`(k + 1)`-th smallest entry. -/
def IsSorting (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : Prop := Monotone (q ∘ σ)

/-- Every vector has a sorting permutation. -/
theorem isSorting_sort (q : Fin m → ℝ) : IsSorting q (Tuple.sort q) := Tuple.monotone_sort q

/-- Every vector has a sorting permutation (existence form of `isSorting_sort`). -/
theorem exists_isSorting (q : Fin m → ℝ) : ∃ σ, IsSorting q σ := ⟨_, isSorting_sort q⟩

/-! ### Positions and counts -/

/-- A downward closed set of positions consists of the first `card` positions. -/
lemma mem_iff_lt_card_of_isLowerSet (S : Finset (Fin m))
    (hS : ∀ x ∈ S, ∀ y, y ≤ x → y ∈ S) (x : Fin m) : x ∈ S ↔ (x : ℕ) < S.card := by
  constructor
  · intro hx
    have hsub : Iic x ⊆ S := fun y hy => hS x hx y (mem_Iic.mp hy)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra hx
    have hsub : S ⊆ Iio x := fun y hy => by
      rw [mem_Iio]
      by_contra hle
      exact hx (hS y hy x (not_lt.mp hle))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- The entry at position `k` is below `v` exactly when `k` is less than the number of entries
below `v`. -/
lemma IsSorting.lt_iff {q : Fin m → ℝ} {σ : Equiv.Perm (Fin m)} (h : IsSorting q σ) (v : ℝ)
    (k : Fin m) : q (σ k) < v ↔ (k : ℕ) < (univ.filter fun l => q l < v).card := by
  have hcard : (univ.filter fun l => q l < v).card
      = (univ.filter fun k : Fin m => q (σ k) < v).card :=
    (Finset.card_equiv σ (by simp)).symm
  rw [hcard, ← mem_iff_lt_card_of_isLowerSet _ (fun x hx y hyx => ?_)]
  · simp
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact (h hyx).trans_lt hx

/-- The entry at position `k` is at most `v` exactly when `k` is less than the number of
entries that are at most `v`. -/
lemma IsSorting.le_iff {q : Fin m → ℝ} {σ : Equiv.Perm (Fin m)} (h : IsSorting q σ) (v : ℝ)
    (k : Fin m) : q (σ k) ≤ v ↔ (k : ℕ) < (univ.filter fun l => q l ≤ v).card := by
  have hcard : (univ.filter fun l => q l ≤ v).card
      = (univ.filter fun k : Fin m => q (σ k) ≤ v).card :=
    (Finset.card_equiv σ (by simp)).symm
  rw [hcard, ← mem_iff_lt_card_of_isLowerSet _ (fun x hx y hyx => ?_)]
  · simp
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact (h hyx).trans hx

/-! ### Holm -/

/-- The first 0-based position `k` whose p-value exceeds `α / (m - k)`; `m` if every position
passes. This is the number of rejections of the textbook Holm procedure. -/
noncomputable def holmStop (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : ℕ :=
  (insert m ((univ.filter fun k : Fin m => α / ((m : ℝ) - (k : ℕ)) < q (σ k)).image
    fun k : Fin m => (k : ℕ))).min' (insert_nonempty _ _)

/-- Textbook Holm step-down: reject the hypotheses `σ 0, …, σ (holmStop - 1)`. -/
noncomputable def holmSorted (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    Finset (Fin m) :=
  (univ.filter fun k : Fin m => (k : ℕ) < holmStop α q σ).image σ

/-- The Holm stopping position is at most `m`. -/
lemma holmStop_le (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : holmStop α q σ ≤ m :=
  Finset.min'_le _ _ (mem_insert_self _ _)

/-- Position `k` is before the stopping position iff all positions up to `k` pass. -/
lemma lt_holmStop_iff (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    (k : ℕ) < holmStop α q σ ↔ ∀ l : Fin m, l ≤ k → q (σ l) ≤ α / ((m : ℝ) - (l : ℕ)) := by
  rw [holmStop, Finset.lt_min'_iff]
  constructor
  · intro h l hl
    by_contra hcon
    have := h l (mem_insert_of_mem (mem_image.mpr ⟨l, by simpa using hcon, rfl⟩))
    exact absurd (Fin.le_def.mp hl) (by omega)
  · intro h y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact k.2
    · obtain ⟨l, hl, rfl⟩ := mem_image.mp hy
      by_contra hcon
      have hlk : l ≤ k := Fin.le_def.mpr (by omega)
      exact absurd (h l hlk) (not_le.mpr (mem_filter.mp hl).2)

/-- If the procedure stops before the end, the stopping position fails its threshold. -/
lemma holmStop_fails (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (h : holmStop α q σ < m) :
    α / ((m : ℝ) - holmStop α q σ) < q (σ ⟨holmStop α q σ, h⟩) := by
  have hmem := Finset.min'_mem (insert m ((univ.filter fun k : Fin m =>
    α / ((m : ℝ) - (k : ℕ)) < q (σ k)).image fun k : Fin m => (k : ℕ))) (insert_nonempty _ _)
  rcases mem_insert.mp hmem with h' | h'
  · exact absurd h' (ne_of_lt h)
  · obtain ⟨l, hl, hl'⟩ := mem_image.mp h'
    have : l = ⟨holmStop α q σ, h⟩ := Fin.ext hl'
    rw [← this, show holmStop α q σ = (l : ℕ) from hl'.symm]
    exact (mem_filter.mp hl).2

/-- Hypothesis `i` is rejected by the textbook Holm rule iff every position up to its own
(`σ.symm i`) passes its threshold `α / (m - l)` (0-based `l`). -/
lemma mem_holmSorted_iff (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    i ∈ holmSorted α q σ
      ↔ ∀ l : Fin m, l ≤ σ.symm i → q (σ l) ≤ α / ((m : ℝ) - (l : ℕ)) := by
  rw [← lt_holmStop_iff, holmSorted, mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa using hk
  · intro h
    exact ⟨σ.symm i, by simpa using h, by simp⟩

/-- The textbook Holm procedure rejects exactly `holmStop` hypotheses. -/
lemma card_holmSorted (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    (holmSorted α q σ).card = holmStop α q σ := by
  rw [holmSorted, Finset.card_image_of_injective _ σ.injective]
  have : (univ.filter fun k : Fin m => (k : ℕ) < holmStop α q σ)
      = (Iio (holmStop α q σ)).attachFin (fun n hn => by
          have := holmStop_le α q σ; rw [mem_Iio] at hn; omega) := by
    ext k; simp
  rw [this, card_attachFin, Nat.card_Iio]

variable {Ω : Type*}

/-- **Textbook Holm equals the sort-free definition.** For `α ≥ 0` and any permutation `σ`
sorting the p-values at `ω`, the step-down rule "reject `σ 0, …, σ (k - 1)`, where `k` is the
first 0-based position with `p (σ k) > α / (m - k)`" rejects exactly `holm α p ω`. -/
theorem holmSorted_eq_holm {α : ℝ} (hα : 0 ≤ α) (p : Fin m → Ω → ℝ) (ω : Ω)
    (σ : Equiv.Perm (Fin m)) (hσ : IsSorting (fun j => p j ω) σ) :
    holmSorted α (fun j => p j ω) σ = holm α p ω := by
  classical
  ext i
  rw [mem_holmSorted_iff]
  simp only [holm, mem_filter, mem_univ, true_and, Fintype.card_fin]
  constructor
  · intro h j hji
    set a := (univ.filter fun l => p l ω < p j ω).card with ha
    -- the position of `j` is at least `a`
    have hj' : a ≤ (σ.symm j : ℕ) := by
      by_contra hcon
      have := (hσ.lt_iff (p j ω) (σ.symm j)).mpr (by omega)
      simp at this
    set A : Fin m := ⟨a, lt_of_le_of_lt hj' (σ.symm j).2⟩ with hA
    have h1 : p j ω ≤ p (σ A) ω := by
      by_contra hcon
      have := (hσ.lt_iff (p j ω) A).mp (not_le.mp hcon)
      exact lt_irrefl a this
    have h2 : p (σ A) ω ≤ p j ω := by
      have := hσ (show A ≤ σ.symm j from Fin.le_def.mpr hj')
      simpa using this
    have hAk : A ≤ σ.symm i := by
      by_contra hcon
      have hlt : ((σ.symm i : Fin m) : ℕ) < a := Fin.lt_def.mp (not_le.mp hcon)
      have := (hσ.lt_iff (p j ω) (σ.symm i)).mpr hlt
      simp only [Equiv.apply_symm_apply] at this
      exact absurd hji (not_le.mpr this)
    have := h A hAk
    simp only [hA] at this
    exact (le_antisymm h1 h2 ▸ this : p j ω ≤ α / ((m : ℝ) - a))
  · intro h l hl
    have hji : p (σ l) ω ≤ p i ω := by
      have := hσ hl
      simpa using this
    have h1 := h (σ l) hji
    set a := (univ.filter fun l' => p l' ω < p (σ l) ω).card with ha
    have hal : a ≤ (l : ℕ) := by
      by_contra hcon
      have := (hσ.lt_iff (p (σ l) ω) l).mpr (by omega)
      simp at this
    refine h1.trans (div_le_div_of_nonneg_left hα ?_ ?_)
    · have : ((l : ℕ) : ℝ) < m := by exact_mod_cast l.2
      linarith
    · have : (a : ℝ) ≤ (l : ℕ) := by exact_mod_cast hal
      linarith

/-! ### Hochberg -/

/-- The largest 1-based position `k + 1` whose p-value is at most `α / (m - (k + 1) + 1)`;
`0` if there is none. This is the number of rejections of the textbook Hochberg procedure. -/
noncomputable def hochbergStop (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : ℕ :=
  univ.sup fun k : Fin m =>
    if q (σ k) ≤ α / ((m : ℝ) - ((k : ℕ) + 1 : ℕ) + 1) then (k : ℕ) + 1 else 0

/-- Textbook Hochberg step-up: reject the hypotheses at the first `hochbergStop` positions. -/
noncomputable def hochbergSorted (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    Finset (Fin m) :=
  (univ.filter fun k : Fin m => (k : ℕ) < hochbergStop α q σ).image σ

/-- The Hochberg stopping position is at most `m`. -/
lemma hochbergStop_le (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    hochbergStop α q σ ≤ m :=
  Finset.sup_le fun k _ => by split_ifs <;> omega

/-- Position `k` is rejected iff some position `l ≥ k` passes its threshold `α / (m - l)`
(0-based). -/
lemma lt_hochbergStop_iff (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    (k : ℕ) < hochbergStop α q σ
      ↔ ∃ l : Fin m, k ≤ l ∧ q (σ l) ≤ α / ((m : ℝ) - (l : ℕ)) := by
  have hthr : ∀ l : Fin m, (m : ℝ) - ((l : ℕ) + 1 : ℕ) + 1 = (m : ℝ) - (l : ℕ) := fun l => by
    push_cast; ring
  rw [hochbergStop, Finset.lt_sup_iff]
  constructor
  · rintro ⟨l, -, hl⟩
    by_cases hc : q (σ l) ≤ α / ((m : ℝ) - ((l : ℕ) + 1 : ℕ) + 1)
    · simp only [hc, ↓reduceIte] at hl
      exact ⟨l, Fin.le_def.mpr (by omega), by rwa [hthr] at hc⟩
    · simp only [hc, ↓reduceIte] at hl; omega
  · rintro ⟨l, hkl, hl⟩
    refine ⟨l, mem_univ _, ?_⟩
    have hc : q (σ l) ≤ α / ((m : ℝ) - ((l : ℕ) + 1 : ℕ) + 1) := by rwa [hthr]
    simp only [hc, ↓reduceIte]
    have := Fin.le_def.mp hkl
    omega

/-- Hypothesis `i` is rejected by the textbook Hochberg rule iff some position at or after its
own (`σ.symm i`) passes its threshold `α / (m - l)` (0-based `l`). -/
lemma mem_hochbergSorted_iff (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    i ∈ hochbergSorted α q σ
      ↔ ∃ l : Fin m, σ.symm i ≤ l ∧ q (σ l) ≤ α / ((m : ℝ) - (l : ℕ)) := by
  rw [← lt_hochbergStop_iff, hochbergSorted, mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa using hk
  · intro h
    exact ⟨σ.symm i, by simpa using h, by simp⟩

/-- The textbook Hochberg procedure rejects exactly `hochbergStop` hypotheses. -/
lemma card_hochbergSorted (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    (hochbergSorted α q σ).card = hochbergStop α q σ := by
  rw [hochbergSorted, Finset.card_image_of_injective _ σ.injective]
  have : (univ.filter fun k : Fin m => (k : ℕ) < hochbergStop α q σ)
      = (Iio (hochbergStop α q σ)).attachFin (fun n hn => by
          have := hochbergStop_le α q σ; rw [mem_Iio] at hn; omega) := by
    ext k; simp
  rw [this, card_attachFin, Nat.card_Iio]

/-- **Textbook Hochberg equals the sort-free definition.** For `α ≥ 0` and any permutation `σ`
sorting the p-values at `ω`, the step-up rule "take the largest 1-based `k` with
`p₍ₖ₎ ≤ α / (m - k + 1)` and reject the hypotheses at positions `1, …, k`" rejects exactly
`hochberg α p ω`. -/
theorem hochbergSorted_eq_hochberg {α : ℝ} (hα : 0 ≤ α) (p : Fin m → Ω → ℝ) (ω : Ω)
    (σ : Equiv.Perm (Fin m)) (hσ : IsSorting (fun j => p j ω) σ) :
    hochbergSorted α (fun j => p j ω) σ = hochberg α p ω := by
  classical
  ext i
  rw [mem_hochbergSorted_iff, mem_hochberg]
  -- the number of p-values above `v` is `m` minus the number of p-values at most `v`
  have hcount : ∀ v : ℝ, ((univ.filter fun l : Fin m => v < p l ω).card : ℝ)
      = (m : ℝ) - (univ.filter fun l : Fin m => p l ω ≤ v).card := by
    intro v
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin m))) (fun l => p l ω ≤ v)
    simp only [not_le, card_univ, Fintype.card_fin] at this
    have h' : (((univ.filter fun l : Fin m => p l ω ≤ v).card
        + (univ.filter fun l : Fin m => v < p l ω).card : ℕ) : ℝ) = m := by exact_mod_cast this
    push_cast at h'
    linarith
  constructor
  · rintro ⟨l, hil, hl⟩
    refine ⟨σ l, ?_, ?_⟩
    · have := hσ hil
      simpa using this
    · rw [hcount]
      have hb := (hσ.le_iff (p (σ l) ω) l).mp le_rfl
      refine hl.trans (div_le_div_of_nonneg_left hα ?_ ?_)
      · have : ((univ.filter fun l' : Fin m => p l' ω ≤ p (σ l) ω).card : ℝ) ≤ m := by
          exact_mod_cast (card_le_univ _).trans (by simp)
        linarith
      · have : ((l : ℕ) : ℝ) + 1 ≤ (univ.filter fun l' : Fin m => p l' ω ≤ p (σ l) ω).card := by
          exact_mod_cast hb
        linarith
  · rintro ⟨j, hij, hj⟩
    rw [hcount] at hj
    set b := (univ.filter fun l : Fin m => p l ω ≤ p j ω).card with hb
    have hjpos : ((σ.symm j : Fin m) : ℕ) < b := by
      have := (hσ.le_iff (p j ω) (σ.symm j)).mp (by simp)
      exact this
    have hbm : b ≤ m := (card_le_univ _).trans (by simp)
    set B : Fin m := ⟨b - 1, by omega⟩ with hB
    have h1 : p (σ B) ω ≤ p j ω := (hσ.le_iff (p j ω) B).mpr (by simp [hB]; omega)
    have hiB : σ.symm i ≤ B := by
      have := (hσ.le_iff (p j ω) (σ.symm i)).mp (by simpa using hij)
      exact Fin.le_def.mpr (by simp only [hB]; omega)
    refine ⟨B, hiB, h1.trans (hj.trans (le_of_eq ?_))⟩
    congr 1
    have : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    simp only [hB, this]
    ring

/-! ### Benjamini–Hochberg -/

/-- The largest 1-based position `k + 1` whose p-value is at most `α (k + 1) / m`; `0` if
there is none. This is the number of rejections of the textbook Benjamini–Hochberg
procedure. -/
noncomputable def bhSortedK (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : ℕ :=
  univ.sup fun k : Fin m =>
    if q (σ k) ≤ α * ((k : ℕ) + 1 : ℕ) / m then (k : ℕ) + 1 else 0

/-- Textbook Benjamini–Hochberg step-up: reject the hypotheses at the first `bhSortedK`
positions. -/
noncomputable def bhSorted (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    Finset (Fin m) :=
  (univ.filter fun k : Fin m => (k : ℕ) < bhSortedK α q σ).image σ

/-- **The textbook cut-off index equals `bhK`**, for every real `α` and every sorting
permutation: the largest `k` with `q₍ₖ₎ ≤ α k / m` is the largest `k` such that at least `k`
of the `q j` are at most `α k / m`. -/
theorem bhSortedK_eq_bhK (α : ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (hσ : IsSorting q σ) : bhSortedK α q σ = bhK α q := by
  have hiff : ∀ k : Fin m, q (σ k) ≤ α * ((k : ℕ) + 1 : ℕ) / m
      ↔ (k : ℕ) + 1 ≤ bhCount α q ((k : ℕ) + 1) := by
    intro k
    rw [hσ.le_iff, bhCount, Fintype.card_fin, Nat.succ_le_iff]
  apply le_antisymm
  · refine Finset.sup_le fun k _ => ?_
    split_ifs with h
    · exact le_bhK q (by simp) ((hiff k).mp h)
    · exact Nat.zero_le _
  · rcases Nat.eq_zero_or_pos (bhK α q) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hle : bhK α q ≤ m := by simpa using bhK_le (α := α) q
      set k : Fin m := ⟨bhK α q - 1, by omega⟩ with hk
      have hk1 : (k : ℕ) + 1 = bhK α q := by simp only [hk]; omega
      have hpass : q (σ k) ≤ α * ((k : ℕ) + 1 : ℕ) / m := by
        rw [hiff, hk1]; exact bhK_le_bhCount q
      have := Finset.le_sup (f := fun k : Fin m =>
        if q (σ k) ≤ α * ((k : ℕ) + 1 : ℕ) / m then (k : ℕ) + 1 else 0) (mem_univ k)
      simp only [hpass, ↓reduceIte] at this
      rw [← hk1]
      exact this

/-- **Textbook Benjamini–Hochberg equals the sort-free definition.** For `α ≥ 0` and any
permutation `σ` sorting `q`, the step-up rule "take the largest 1-based `k` with
`q₍ₖ₎ ≤ α k / m` and reject the hypotheses at positions `1, …, k`" rejects exactly
`bhReject α q`. -/
theorem bhSorted_eq_bhReject {α : ℝ} (hα : 0 ≤ α) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (hσ : IsSorting q σ) : bhSorted α q σ = bhReject α q := by
  ext i
  have hcard := card_bhReject hα q
  rw [bhSorted, bhSortedK_eq_bhK α q σ hσ, mem_image]
  have key : i ∈ bhReject α q ↔ ((σ.symm i : Fin m) : ℕ) < bhK α q := by
    rw [← hcard, bhReject, mem_filter]
    have := hσ.le_iff (α * bhK α q / Fintype.card (Fin m)) (σ.symm i)
    simp only [Equiv.apply_symm_apply] at this
    simpa using this
  rw [key]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa using hk
  · intro h
    exact ⟨σ.symm i, by simpa using h, by simp⟩

/-- The textbook Benjamini–Hochberg procedure rejects `bhSortedK` hypotheses. -/
lemma card_bhSorted {α : ℝ} (hα : 0 ≤ α) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (hσ : IsSorting q σ) : (bhSorted α q σ).card = bhSortedK α q σ := by
  rw [bhSorted_eq_bhReject hα q σ hσ, card_bhReject hα, bhSortedK_eq_bhK α q σ hσ]

/-! ### Independence of the sorting permutation -/

/-- The sorted rules do not depend on which sorting permutation is used (for `α ≥ 0`). -/
theorem holmSorted_eq_of_isSorting {α : ℝ} (hα : 0 ≤ α) (q : Fin m → ℝ)
    {σ τ : Equiv.Perm (Fin m)} (hσ : IsSorting q σ) (hτ : IsSorting q τ) :
    holmSorted α q σ = holmSorted α q τ :=
  (holmSorted_eq_holm hα (fun j (_ : Unit) => q j) () σ hσ).trans
    (holmSorted_eq_holm hα (fun j (_ : Unit) => q j) () τ hτ).symm

/-- For `α ≥ 0` the textbook Hochberg rule does not depend on how tied p-values are ordered:
any two sorting permutations give the same rejection set. -/
theorem hochbergSorted_eq_of_isSorting {α : ℝ} (hα : 0 ≤ α) (q : Fin m → ℝ)
    {σ τ : Equiv.Perm (Fin m)} (hσ : IsSorting q σ) (hτ : IsSorting q τ) :
    hochbergSorted α q σ = hochbergSorted α q τ :=
  (hochbergSorted_eq_hochberg hα (fun j (_ : Unit) => q j) () σ hσ).trans
    (hochbergSorted_eq_hochberg hα (fun j (_ : Unit) => q j) () τ hτ).symm

/-- For `α ≥ 0` the textbook Benjamini–Hochberg rule does not depend on how tied p-values are
ordered: any two sorting permutations give the same rejection set. -/
theorem bhSorted_eq_of_isSorting {α : ℝ} (hα : 0 ≤ α) (q : Fin m → ℝ)
    {σ τ : Equiv.Perm (Fin m)} (hσ : IsSorting q σ) (hτ : IsSorting q τ) :
    bhSorted α q σ = bhSorted α q τ :=
  (bhSorted_eq_bhReject hα q σ hσ).trans (bhSorted_eq_bhReject hα q τ hτ).symm

end Applied.MultipleTesting
