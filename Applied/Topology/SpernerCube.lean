import Mathlib

/-!
# A Sperner-type lemma for the Kuhn triangulation of the cube

The grid `{0, …, N}^m` is cut into Kuhn simplices: a simplex is given by a base point
`v : Fin m → Fin N` (so `v i < N`) and a permutation `r` of the coordinates ("ranks"); its
vertices are `vertex (v, r) k = v + 𝟙{i : k ≤ r i}` for `k = 0, …, m`.

A labelling `l : (Fin m → ℕ) → Fin (m + 1)` is *admissible* if
(A) `x i = 0 → l x ≠ castSucc i` and (B) `x i = N → l x ≠ last m`.
`sperner_cube` : for `0 < N`, the number of fully labelled Kuhn simplices is odd.
-/

namespace Applied.Topology.Kuhn

open Finset

/-- A Kuhn simplex of the grid `{0,…,N}^m`: base point and rank permutation. -/
abbrev Simp (m N : ℕ) := (Fin m → Fin N) × Equiv.Perm (Fin m)

/-- The `k`-th vertex of a Kuhn simplex: `vertex (v, r) k i = v i + [k ≤ r i]`. -/
def ind {m : ℕ} (k : Fin (m + 1)) (t : Fin m) : ℕ := if k.val ≤ t.val then 1 else 0

lemma ind_le_one {m : ℕ} (k : Fin (m + 1)) (t : Fin m) : ind k t ≤ 1 := by
  unfold ind; split_ifs <;> omega

/-- The `k`-th vertex of a Kuhn simplex: `vertex (v, r) k i = v i + [k ≤ r i]`. -/
def vertex {m N : ℕ} (σ : Simp m N) (k : Fin (m + 1)) : Fin m → ℕ :=
  fun i => (σ.1 i : ℕ) + ind k (σ.2 i)

lemma vertex_le {m N : ℕ} (σ : Simp m N) (k : Fin (m + 1)) (i : Fin m) :
    vertex σ k i ≤ N := by
  have := (σ.1 i).isLt
  have := ind_le_one k (σ.2 i)
  unfold vertex; omega

lemma vertex_ge {m N : ℕ} (σ : Simp m N) (k : Fin (m + 1)) (i : Fin m) :
    (σ.1 i : ℕ) ≤ vertex σ k i := by
  unfold vertex; omega

lemma vertex_le_base {m N : ℕ} (σ : Simp m N) (k : Fin (m + 1)) (i : Fin m) :
    vertex σ k i ≤ (σ.1 i : ℕ) + 1 := by
  have := ind_le_one k (σ.2 i)
  unfold vertex; omega

/-! ### The local parity lemma -/

theorem local_parity {α : Type*} [Fintype α] [DecidableEq α] (g : α → α) (c : α) :
    (∑ k, if (univ.erase k).image g = univ.erase c then (1 : ZMod 2) else 0) =
      if univ.image g = univ then 1 else 0 := by
  by_cases hg : Function.Injective g
  · have hs : Function.Surjective g := Finite.injective_iff_surjective.1 hg
    have himg : univ.image g = univ := Finset.image_univ_of_surjective hs
    rw [ite_eq_left himg]
    obtain ⟨k0, hk0⟩ := hs c
    rw [Finset.sum_eq_single k0]
    · rw [ite_eq_left (by rw [Finset.image_erase hg, himg, hk0])]
    · intro k _ hk
      refine ite_eq_right fun h => ?_
      rw [Finset.image_erase hg, himg] at h
      apply hk
      apply hg
      rw [hk0]
      by_contra hne
      have : c ∈ univ.erase (g k) := Finset.mem_erase.2 ⟨Ne.symm hne, mem_univ _⟩
      rw [h] at this
      simp at this
    · intro h; exact absurd (mem_univ _) h
  · have hnot : ¬ univ.image g = univ := by
      intro h
      apply hg
      apply Finite.injective_iff_surjective.2
      intro y
      have : y ∈ univ.image g := by rw [h]; exact mem_univ y
      simpa using this
    rw [ite_eq_right hnot]
    obtain ⟨p, q, hpq, hne⟩ : ∃ p q, g p = g q ∧ p ≠ q := by
      simp only [Function.Injective, not_forall] at hg
      obtain ⟨p, q, h1, h2⟩ := hg
      exact ⟨p, q, h1, h2⟩
    have himg : ∀ x y, g x = g y → x ≠ y → (univ.erase x).image g = univ.image g := by
      intro x y hxy hne
      apply Finset.Subset.antisymm (Finset.image_subset_image (erase_subset _ _))
      intro z hz
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hz
      by_cases hw : w = x
      · subst hw; exact Finset.mem_image.2 ⟨y, mem_erase.2 ⟨hne.symm, mem_univ _⟩, hxy.symm⟩
      · exact Finset.mem_image.2 ⟨w, mem_erase.2 ⟨hw, mem_univ _⟩, rfl⟩
    rw [← Finset.sum_subset (subset_univ {p, q})]
    · rw [Finset.sum_pair hne, himg p q hpq hne, himg q p hpq.symm hne.symm]
      split_ifs <;> decide
    · intro k _ hk
      simp only [mem_insert, mem_singleton, not_or] at hk
      refine ite_eq_right fun h => ?_
      have hsub : (univ.erase k).image g ⊆ ((univ.erase k).erase p).image g := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
        by_cases hwp : w = p
        · subst hwp
          exact Finset.mem_image.2 ⟨q, by simp [hne.symm, Ne.symm hk.2], hpq.symm⟩
        · exact Finset.mem_image.2 ⟨w, mem_erase.2 ⟨hwp, hw⟩, rfl⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_image_le (s := (univ.erase k).erase p) (f := g)
      rw [h] at h1
      have hp : p ∈ univ.erase k := mem_erase.2 ⟨Ne.symm hk.1, mem_univ _⟩
      rw [Finset.card_erase_of_mem hp, Finset.card_erase_of_mem (mem_univ _)] at h2
      rw [Finset.card_erase_of_mem (mem_univ _)] at h1
      have h3 : 1 < (univ : Finset α).card :=
        Finset.one_lt_card.2 ⟨p, mem_univ _, q, mem_univ _, hne⟩
      omega

/-! ### Images over `univ.erase 0` and `univ.erase (last _)` -/

lemma image_erase_zero {β : Type*} [DecidableEq β] {n : ℕ} (f : Fin (n + 1) → β) :
    (univ.erase 0).image f = univ.image (fun j : Fin n => f j.succ) := by
  ext y
  simp only [mem_image, mem_erase, mem_univ, and_true, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.pred ha, by simp⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b.succ, Fin.succ_ne_zero b, rfl⟩

lemma image_erase_last {β : Type*} [DecidableEq β] {n : ℕ} (f : Fin (n + 1) → β) :
    (univ.erase (Fin.last n)).image f = univ.image (fun j : Fin n => f j.castSucc) := by
  ext y
  simp only [mem_image, mem_erase, mem_univ, and_true, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.castPred ha, by simp⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b.castSucc, Fin.castSucc_ne_last b, rfl⟩

/-! ### Neighbouring simplices across a facet -/

variable {n N : ℕ}

lemma finRotate_symm_zero : (finRotate (n + 1)).symm 0 = Fin.last n := by
  rw [Equiv.symm_apply_eq, finRotate_last]

/-- Across the facet opposite vertex `0` (needs `v i₀ > 0` where `r i₀ = 0`). -/
def down (σ : Simp (n + 1) N) (_hv : 0 < (σ.1 (σ.2.symm 0) : ℕ)) : Simp (n + 1) N :=
  (Function.update σ.1 (σ.2.symm 0)
      ⟨σ.1 (σ.2.symm 0) - 1, lt_of_le_of_lt (Nat.sub_le _ _) (Fin.isLt _)⟩,
    σ.2.trans (finRotate (n + 1)).symm)

/-- Across the facet opposite vertex `last` (needs `v i₁ + 1 < N` where `r i₁ = last`). -/
def up (σ : Simp (n + 1) N) (hv : (σ.1 (σ.2.symm (Fin.last n)) : ℕ) + 1 < N) :
    Simp (n + 1) N :=
  (Function.update σ.1 (σ.2.symm (Fin.last n)) ⟨_, hv⟩, σ.2.trans (finRotate (n + 1)))

/-- Across the facet opposite an inner vertex `k`: swap the ranks `k - 1` and `k`. -/
def swp (σ : Simp (n + 1) N) (k : Fin (n + 2)) (hl : k ≠ Fin.last (n + 1)) : Simp (n + 1) N :=
  (σ.1, σ.2.trans (Equiv.swap ⟨k.val - 1, by have := k.isLt; omega⟩ (k.castPred hl)))

lemma vertex_down (σ : Simp (n + 1) N) (hv : 0 < (σ.1 (σ.2.symm 0) : ℕ)) (j : Fin (n + 1)) :
    vertex (down σ hv) j.castSucc = vertex σ j.succ := by
  funext i
  simp only [vertex, down, Equiv.trans_apply]
  by_cases hi : i = σ.2.symm 0
  · subst hi
    simp only [Function.update_self, Equiv.apply_symm_apply, finRotate_symm_zero, ind,
      Fin.val_last, Fin.val_zero, Fin.val_castSucc, Fin.val_succ]
    have := j.isLt
    rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    omega
  · rw [Function.update_of_ne hi]
    have hr : σ.2 i ≠ 0 := fun h => hi (by rw [← h, Equiv.symm_apply_apply])
    have e := coe_finRotate_symm_of_ne_zero hr
    have : 0 < (σ.2 i).val := by
      rcases Nat.eq_zero_or_pos (σ.2 i).val with h | h
      · exact absurd (Fin.ext h) hr
      · exact h
    congr 1
    simp only [ind, Fin.val_castSucc, Fin.val_succ, e]
    split_ifs <;> omega

lemma vertex_up (σ : Simp (n + 1) N) (hv : (σ.1 (σ.2.symm (Fin.last n)) : ℕ) + 1 < N)
    (j : Fin (n + 1)) : vertex (up σ hv) j.succ = vertex σ j.castSucc := by
  funext i
  simp only [vertex, up, Equiv.trans_apply]
  by_cases hi : i = σ.2.symm (Fin.last n)
  · subst hi
    simp only [Function.update_self, Equiv.apply_symm_apply, finRotate_last, ind, Fin.val_last,
      Fin.val_zero, Fin.val_castSucc, Fin.val_succ]
    have := j.isLt
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  · rw [Function.update_of_ne hi]
    have hr : σ.2 i ≠ Fin.last n := fun h => hi (by rw [← h, Equiv.symm_apply_apply])
    have e : (finRotate (n + 1) (σ.2 i) : ℕ) = (σ.2 i : ℕ) + 1 := by
      rw [coe_finRotate, ite_eq_right hr]
    congr 1
    simp only [ind, Fin.val_castSucc, Fin.val_succ, e]
    split_ifs <;> omega

lemma vertex_swp (σ : Simp (n + 1) N) (k : Fin (n + 2)) (hl : k ≠ Fin.last (n + 1))
    (hk : k ≠ 0) (j : Fin (n + 2)) (hj : j ≠ k) : vertex (swp σ k hl) j = vertex σ j := by
  funext i
  simp only [vertex, swp, Equiv.trans_apply]
  congr 1
  have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
  have hj' : j.val ≠ k.val := fun h => hj (Fin.ext h)
  have := k.isLt
  simp only [ind]
  generalize σ.2 i = t
  by_cases h1 : t.val = k.val - 1
  · have ht : t = ⟨k.val - 1, by omega⟩ := Fin.ext h1
    rw [ht, Equiv.swap_apply_left]
    simp only [Fin.coe_castPred]
    exact if_congr ⟨fun _ => by omega, fun _ => by omega⟩ rfl rfl
  · by_cases h2 : t.val = k.val
    · have ht : t = k.castPred hl := Fin.ext (by simp [h2])
      rw [ht, Equiv.swap_apply_right]
      simp only [Fin.coe_castPred]
      exact if_congr ⟨fun _ => by omega, fun _ => by omega⟩ rfl rfl
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]; simp))]

lemma swp_ne (σ : Simp (n + 1) N) (k : Fin (n + 2)) (hl : k ≠ Fin.last (n + 1))
    (hk : k ≠ 0) : swp σ k hl ≠ σ := by
  intro h
  have h2 := congrArg (fun τ : Simp (n + 1) N => τ.2 (σ.2.symm ⟨k.val - 1, by
    have := k.isLt; omega⟩)) h
  simp only [swp, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left] at h2
  have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
  have := congrArg Fin.val h2
  simp at this
  omega

lemma last_ne_zero' : (Fin.last (n + 1)) ≠ 0 := by simp [Fin.ext_iff]

/-- The neighbour map on (simplex, dropped vertex) pairs: the other simplex containing the
same facet, with its dropped vertex. Fixed points are exactly the facets on the boundary. -/
def nb (x : Simp (n + 1) N × Fin (n + 2)) : Simp (n + 1) N × Fin (n + 2) :=
  if x.2 = 0 then
    if hv : 0 < (x.1.1 (x.1.2.symm 0) : ℕ) then (down x.1 hv, Fin.last (n + 1)) else x
  else if hl : x.2 = Fin.last (n + 1) then
    if hv : (x.1.1 (x.1.2.symm (Fin.last n)) : ℕ) + 1 < N then (up x.1 hv, 0) else x
  else (swp x.1 x.2 hl, x.2)

lemma nb_zero_pos (σ : Simp (n + 1) N) (hv : 0 < (σ.1 (σ.2.symm 0) : ℕ)) :
    nb (σ, 0) = (down σ hv, Fin.last (n + 1)) := by simp [nb, hv]

lemma nb_zero_neg (σ : Simp (n + 1) N) (hv : ¬ 0 < (σ.1 (σ.2.symm 0) : ℕ)) :
    nb (σ, 0) = (σ, 0) := by simp [nb, hv]

lemma nb_last_pos (σ : Simp (n + 1) N) (hv : (σ.1 (σ.2.symm (Fin.last n)) : ℕ) + 1 < N) :
    nb (σ, Fin.last (n + 1)) = (up σ hv, 0) := by simp [nb, hv]

lemma nb_last_neg (σ : Simp (n + 1) N) (hv : ¬ (σ.1 (σ.2.symm (Fin.last n)) : ℕ) + 1 < N) :
    nb (σ, Fin.last (n + 1)) = (σ, Fin.last (n + 1)) := by simp [nb, hv]

lemma nb_mid (σ : Simp (n + 1) N) (k : Fin (n + 2)) (_h0 : k ≠ 0) (hl : k ≠ Fin.last (n + 1)) :
    nb (σ, k) = (swp σ k hl, k) := by simp [nb, _h0, hl]

/-- The facet of `x.1` opposite the vertex `x.2`, as a set of grid points. -/
def facet {m : ℕ} (x : Simp m N × Fin (m + 1)) : Finset (Fin m → ℕ) :=
  (univ.erase x.2).image (vertex x.1)

lemma facet_nb (x : Simp (n + 1) N × Fin (n + 2)) : facet (nb x) = facet x := by
  obtain ⟨σ, k⟩ := x
  by_cases h0 : k = 0
  · subst h0
    by_cases hv : 0 < (σ.1 (σ.2.symm 0) : ℕ)
    · rw [nb_zero_pos σ hv]
      simp only [facet]
      rw [image_erase_last, image_erase_zero]
      simp only [vertex_down]
    · rw [nb_zero_neg σ hv]
  · by_cases hl : k = Fin.last (n + 1)
    · subst hl
      by_cases hv : (σ.1 (σ.2.symm (Fin.last n)) : ℕ) + 1 < N
      · rw [nb_last_pos σ hv]
        simp only [facet]
        rw [image_erase_last, image_erase_zero]
        simp only [vertex_up]
      · rw [nb_last_neg σ hv]
    · rw [nb_mid σ k h0 hl]
      simp only [facet]
      apply Finset.image_congr
      intro j hj
      exact vertex_swp σ k hl h0 j (Finset.ne_of_mem_erase hj)

lemma up_down (σ : Simp (n + 1) N) (hv : 0 < (σ.1 (σ.2.symm 0) : ℕ))
    (hv' : ((down σ hv).1 ((down σ hv).2.symm (Fin.last n)) : ℕ) + 1 < N) :
    up (down σ hv) hv' = σ := by
  have hidx : (down σ hv).2.symm (Fin.last n) = σ.2.symm 0 := by
    simp [down]
  apply Prod.ext
  · funext i
    apply Fin.ext
    simp only [up, Function.update_apply, hidx]
    split_ifs with h
    · subst h; simp only [down, Function.update_self]; omega
    · simp [down, Function.update_of_ne h]
  · apply Equiv.ext; intro i; simp [up, down]

lemma down_up (σ : Simp (n + 1) N) (hv : (σ.1 (σ.2.symm (Fin.last n)) : ℕ) + 1 < N)
    (hv' : 0 < ((up σ hv).1 ((up σ hv).2.symm 0) : ℕ)) :
    down (up σ hv) hv' = σ := by
  have hidx : (up σ hv).2.symm 0 = σ.2.symm (Fin.last n) := by
    rw [show (up σ hv).2 = σ.2.trans (finRotate (n + 1)) from rfl, Equiv.symm_trans_apply,
      finRotate_symm_zero]
  apply Prod.ext
  · funext i
    apply Fin.ext
    simp only [down, Function.update_apply, hidx]
    split_ifs with h
    · subst h; simp only [up, Function.update_self]; omega
    · simp [up, Function.update_of_ne h]
  · apply Equiv.ext; intro i; simp [up, down]

lemma nb_nb (x : Simp (n + 1) N × Fin (n + 2)) : nb (nb x) = x := by
  obtain ⟨σ, k⟩ := x
  by_cases h0 : k = 0
  · subst h0
    by_cases hv : 0 < (σ.1 (σ.2.symm 0) : ℕ)
    · rw [nb_zero_pos σ hv]
      have hidx : (down σ hv).2.symm (Fin.last n) = σ.2.symm 0 := by
        simp [down]
      have hv' : ((down σ hv).1 ((down σ hv).2.symm (Fin.last n)) : ℕ) + 1 < N := by
        rw [hidx]; simp only [down, Function.update_self]
        have := (σ.1 (σ.2.symm 0)).isLt; omega
      rw [nb_last_pos _ hv', up_down]
    · rw [nb_zero_neg σ hv, nb_zero_neg σ hv]
  · by_cases hl : k = Fin.last (n + 1)
    · subst hl
      by_cases hv : (σ.1 (σ.2.symm (Fin.last n)) : ℕ) + 1 < N
      · rw [nb_last_pos σ hv]
        have hidx : (up σ hv).2.symm 0 = σ.2.symm (Fin.last n) := by
          rw [show (up σ hv).2 = σ.2.trans (finRotate (n + 1)) from rfl, Equiv.symm_trans_apply,
      finRotate_symm_zero]
        have hv' : 0 < ((up σ hv).1 ((up σ hv).2.symm 0) : ℕ) := by
          rw [hidx]; simp only [up, Function.update_self]; omega
        rw [nb_zero_pos _ hv', down_up]
      · rw [nb_last_neg σ hv, nb_last_neg σ hv]
    · rw [nb_mid σ k h0 hl, nb_mid _ k h0 hl]
      congr 1
      apply Prod.ext
      · rfl
      · apply Equiv.ext; intro i; simp [swp]

/-- Fixed points of `nb` are boundary facets. -/
lemma nb_eq_self {x : Simp (n + 1) N × Fin (n + 2)} (h : nb x = x) :
    (x.2 = 0 ∧ ¬ 0 < (x.1.1 (x.1.2.symm 0) : ℕ)) ∨
      (x.2 = Fin.last (n + 1) ∧ ¬ (x.1.1 (x.1.2.symm (Fin.last n)) : ℕ) + 1 < N) := by
  obtain ⟨σ, k⟩ := x
  by_cases h0 : k = 0
  · subst h0
    by_cases hv : 0 < (σ.1 (σ.2.symm 0) : ℕ)
    · rw [nb_zero_pos σ hv] at h
      exact absurd (congrArg Prod.snd h) last_ne_zero'
    · exact Or.inl ⟨rfl, hv⟩
  · by_cases hl : k = Fin.last (n + 1)
    · subst hl
      by_cases hv : (σ.1 (σ.2.symm (Fin.last n)) : ℕ) + 1 < N
      · rw [nb_last_pos σ hv] at h
        exact absurd (congrArg Prod.snd h).symm last_ne_zero'
      · exact Or.inr ⟨rfl, hv⟩
    · rw [nb_mid σ k h0 hl] at h
      exact absurd (congrArg Prod.fst h) (swp_ne σ k hl h0)

/-! ### The face `x 0 = 0` -/

open Equiv.Perm in
lemma decomposeFin_eq (r : Equiv.Perm (Fin (n + 1))) (h : r 0 = 0) :
    decomposeFin.symm (0, (decomposeFin r).2) = r := by
  have hq : (decomposeFin r).1 = 0 := by
    have := decomposeFin_symm_apply_zero (decomposeFin r).1 (decomposeFin r).2
    rw [Prod.mk.eta, Equiv.symm_apply_apply] at this
    rw [← this, h]
  calc decomposeFin.symm (0, (decomposeFin r).2)
      = decomposeFin.symm ((decomposeFin r).1, (decomposeFin r).2) := by rw [hq]
    _ = r := by rw [Prod.mk.eta, Equiv.symm_apply_apply]

open Equiv.Perm in
lemma perm_succ_of_zero (r : Equiv.Perm (Fin (n + 1))) (h : r 0 = 0) (i : Fin n) :
    r i.succ = ((decomposeFin r).2 i).succ := by
  conv_lhs => rw [← decomposeFin_eq r h]
  rw [decomposeFin_symm_apply_succ]
  simp

lemma vertex_succ_face (σ : Simp (n + 1) N) (h0 : σ.2 0 = 0) (hv : (σ.1 0 : ℕ) = 0)
    (j : Fin (n + 1)) :
    vertex σ j.succ =
      (Fin.cons (0 : ℕ) (vertex (Fin.tail σ.1, (Equiv.Perm.decomposeFin σ.2).2) j) :
        Fin (n + 1) → ℕ) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [vertex, ind, h0, hv]
  · simp only [vertex, Fin.cons_succ, Fin.tail, perm_succ_of_zero σ.2 h0, ind, Fin.val_succ]
    congr 1
    exact if_congr ⟨fun _ => by omega, fun _ => by omega⟩ rfl rfl

lemma image_eq_erase_zero_iff {ι : Type*} [Fintype ι] (g : ι → Fin (n + 2))
    (hg : ∀ j, g j ≠ 0) :
    univ.image g = univ.erase 0 ↔ univ.image (fun j => (g j).pred (hg j)) = univ := by
  have e1 : univ.image g = (univ.image (fun j => (g j).pred (hg j))).image Fin.succ := by
    rw [image_image]; congr 1; funext j; simp
  have e2 : univ.erase (0 : Fin (n + 2)) = (univ : Finset (Fin (n + 1))).image Fin.succ := by
    have := image_erase_zero (n := n + 1) (id : Fin (n + 2) → Fin (n + 2))
    simpa using this
  rw [e1, e2]
  exact (Finset.image_injective (Fin.succ_injective _)).eq_iff

/-! ### The main parity theorem -/

/-- Boundary conditions on a labelling of the grid `{0,…,N}^m` by `Fin (m + 1)`. -/
def Admissible {m : ℕ} (N : ℕ) (l : (Fin m → ℕ) → Fin (m + 1)) : Prop :=
  (∀ x i, x i = 0 → l x ≠ i.castSucc) ∧ (∀ x i, x i = N → l x ≠ Fin.last m)

/-- A Kuhn simplex is fully labelled if its vertices carry all `m + 1` labels. -/
def full {m : ℕ} (l : (Fin m → ℕ) → Fin (m + 1)) (σ : Simp m N) : Prop :=
  univ.image (fun k => l (vertex σ k)) = univ

/-- A door: a facet whose labels are exactly all labels except `0`. -/
def door {m : ℕ} (l : (Fin m → ℕ) → Fin (m + 1)) (x : Simp m N × Fin (m + 1)) : Prop :=
  (univ.erase x.2).image (fun k => l (vertex x.1 k)) = univ.erase 0

instance {m : ℕ} (l : (Fin m → ℕ) → Fin (m + 1)) : DecidablePred (full (N := N) l) :=
  fun σ => by unfold full; infer_instance

instance {m : ℕ} (l : (Fin m → ℕ) → Fin (m + 1)) : DecidablePred (door (N := N) l) :=
  fun x => by unfold door; infer_instance

lemma door_iff_facet {m : ℕ} (l : (Fin m → ℕ) → Fin (m + 1)) (x : Simp m N × Fin (m + 1)) :
    door l x ↔ (facet x).image l = univ.erase 0 := by
  simp only [door, facet, image_image]; rfl

/-- The face labelling. -/
def faceLabel (l : (Fin (n + 1) → ℕ) → Fin (n + 2)) (hl : Admissible N l) :
    (Fin n → ℕ) → Fin (n + 1) :=
  fun w => (l (Fin.cons (0 : ℕ) w)).pred (by
    have := hl.1 (Fin.cons (0 : ℕ) w) 0 (by simp)
    simpa using this)

lemma faceLabel_admissible (l : (Fin (n + 1) → ℕ) → Fin (n + 2)) (hl : Admissible N l) :
    Admissible N (faceLabel l hl) := by
  constructor
  · intro w i hw h
    have h' : l (Fin.cons (0 : ℕ) w) = i.succ.castSucc := by
      rw [← Fin.succ_castSucc, ← h]; simp [faceLabel]
    exact hl.1 _ i.succ (by simp [hw]) h'
  · intro w i hw h
    have h' : l (Fin.cons (0 : ℕ) w) = Fin.last (n + 1) := by
      rw [← Fin.succ_last, ← h]; simp [faceLabel]
    exact hl.2 _ i.succ (by simp [hw]) h'

lemma door_iff_full_face (l : (Fin (n + 1) → ℕ) → Fin (n + 2)) (hl : Admissible N l)
    (σ : Simp (n + 1) N) (h0 : σ.2 0 = 0) (hv : (σ.1 0 : ℕ) = 0) :
    door l (σ, 0) ↔
      full (faceLabel l hl) ((Fin.tail σ.1, (Equiv.Perm.decomposeFin σ.2).2) : Simp n N) := by
  simp only [door, full]
  rw [image_erase_zero]
  simp only [vertex_succ_face σ h0 hv]
  exact image_eq_erase_zero_iff _ _

lemma nb_eq_self_iff (l : (Fin (n + 1) → ℕ) → Fin (n + 2)) (hl : Admissible N l)
    (x : Simp (n + 1) N × Fin (n + 2)) (hD : door l x) :
    nb x = x ↔ (x.2 = 0 ∧ x.1.2 0 = 0 ∧ (x.1.1 0 : ℕ) = 0) := by
  obtain ⟨σ, k⟩ := x
  constructor
  · intro h
    rcases nb_eq_self h with ⟨hk, hv⟩ | ⟨hk, hv⟩
    · simp only at hk hv
      subst hk
      have hi0 : σ.2.symm 0 = 0 := by
        by_contra hne
        have hmem : (σ.2.symm 0).castSucc ∈ univ.erase (0 : Fin (n + 2)) := by
          refine mem_erase.2 ⟨?_, mem_univ _⟩
          intro h; apply hne; exact Fin.castSucc_eq_zero_iff.1 h
        rw [← hD] at hmem
        obtain ⟨j, hj, hlj⟩ := mem_image.1 hmem
        have hj0 : j ≠ 0 := ne_of_mem_erase hj
        apply hl.1 (vertex σ j) (σ.2.symm 0) _ hlj
        simp only [vertex, Equiv.apply_symm_apply, ind, Fin.val_zero]
        have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        rw [ite_eq_right (by omega)]
        omega
      refine ⟨rfl, ?_, ?_⟩
      · simpa using (congrArg σ.2 hi0).symm
      · show (σ.1 0 : ℕ) = 0
        rw [hi0] at hv; omega
    · simp only at hk hv
      subst hk
      exfalso
      have hmem : Fin.last (n + 1) ∈ univ.erase (0 : Fin (n + 2)) :=
        mem_erase.2 ⟨last_ne_zero', mem_univ _⟩
      rw [← hD] at hmem
      obtain ⟨j, hj, hlj⟩ := mem_image.1 hmem
      have hjl : j ≠ Fin.last (n + 1) := ne_of_mem_erase hj
      apply hl.2 (vertex σ j) (σ.2.symm (Fin.last n)) _ hlj
      simp only [vertex, Equiv.apply_symm_apply, ind, Fin.val_last]
      have : j.val ≠ n + 1 := fun h => hjl (Fin.ext h)
      have := j.isLt
      have := (σ.1 (σ.2.symm (Fin.last n))).isLt
      rw [ite_eq_left (by omega)]
      omega
  · rintro ⟨hk, h0, hv⟩
    simp only at hk h0 hv
    subst hk
    have hi0 : σ.2.symm 0 = 0 := by rw [Equiv.symm_apply_eq, h0]
    apply nb_zero_neg
    rw [hi0, hv]; omega

theorem sperner_parity (hN : 0 < N) : ∀ (m : ℕ) (l : (Fin m → ℕ) → Fin (m + 1)),
    Admissible N l → (∑ σ : Simp m N, if full l σ then (1 : ZMod 2) else 0) = 1 := by
  intro m
  induction m with
  | zero =>
    intro l _
    have hfull : ∀ σ : Simp 0 N, full l σ := by
      intro σ
      unfold full
      apply Finset.eq_univ_of_forall
      intro y
      exact mem_image.2 ⟨0, mem_univ _, Fin.ext (by
        have := (l (vertex σ 0)).isLt; have := y.isLt; omega)⟩
    simp only [hfull, ite_true, Finset.sum_const, card_univ]
    simp
  | succ n ih =>
    intro l hl
    classical
    -- Step 1: local parity
    have h1 : (∑ σ : Simp (n + 1) N, if full l σ then (1 : ZMod 2) else 0) =
        ∑ x : Simp (n + 1) N × Fin (n + 2), if door l x then (1 : ZMod 2) else 0 := by
      symm
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact local_parity (fun k => l (vertex σ k)) 0
    -- Step 2: interior doors cancel
    have h2 : (∑ x : Simp (n + 1) N × Fin (n + 2), if door l x then (1 : ZMod 2) else 0) =
        ∑ x ∈ univ.filter (fun x : Simp (n + 1) N × Fin (n + 2) => nb x = x), if door l x then (1 : ZMod 2) else 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not univ
        (fun x : Simp (n + 1) N × Fin (n + 2) => nb x = x)]
      have : (∑ x ∈ univ.filter (fun x : Simp (n + 1) N × Fin (n + 2) => ¬ nb x = x),
          if door l x then (1 : ZMod 2) else 0) = 0 := by
        refine Finset.sum_involution (fun x _ => nb x) ?_ ?_ ?_ ?_
        · intro a _
          have : door l (nb a) ↔ door l a := by
            rw [door_iff_facet, door_iff_facet, facet_nb]
          simp only [this]
          split_ifs <;> decide
        · intro a ha _
          exact (mem_filter.1 ha).2
        · intro a ha
          refine mem_filter.2 ⟨mem_univ _, ?_⟩
          rw [nb_nb]
          exact fun h => (mem_filter.1 ha).2 h.symm
        · intro a _
          exact nb_nb a
      rw [this, add_zero]
    -- Step 3: boundary doors lie on the face `x 0 = 0`
    have h3 : (∑ x ∈ univ.filter (fun x : Simp (n + 1) N × Fin (n + 2) => nb x = x), if door l x then (1 : ZMod 2) else 0) =
        ∑ x : Simp (n + 1) N × Fin (n + 2),
          if (x.2 = 0 ∧ x.1.2 0 = 0 ∧ (x.1.1 0 : ℕ) = 0) ∧ door l x then (1 : ZMod 2) else 0 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hD : door l x
      · simp only [nb_eq_self_iff l hl x hD, hD, and_true, ↓reduceIte]
      · simp [hD]
    -- Step 4: they correspond to the fully labelled simplices of the face
    have h4 : (∑ x : Simp (n + 1) N × Fin (n + 2),
          if (x.2 = 0 ∧ x.1.2 0 = 0 ∧ (x.1.1 0 : ℕ) = 0) ∧ door l x then (1 : ZMod 2) else 0) =
        ∑ τ : Simp n N, if full (faceLabel l hl) τ then (1 : ZMod 2) else 0 := by
      rw [Finset.sum_boole, Finset.sum_boole]
      congr 1
      refine Finset.card_nbij' (fun x => ((Fin.tail x.1.1, (Equiv.Perm.decomposeFin x.1.2).2) :
          Simp n N))
        (fun τ => (((Fin.cons (⟨0, hN⟩ : Fin N) τ.1 : Fin (n + 1) → Fin N),
          Equiv.Perm.decomposeFin.symm (0, τ.2)), 0)) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
        obtain ⟨⟨hk, h0, hv⟩, hD⟩ := hx
        obtain ⟨σ, k⟩ := x
        simp only at hk h0 hv ⊢
        subst hk
        exact (door_iff_full_face l hl σ h0 hv).1 hD
      · intro τ hτ
        simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hτ
        rw [Finset.mem_coe, mem_filter]
        refine ⟨mem_univ _, ⟨rfl, by simp, by simp⟩, ?_⟩
        rw [door_iff_full_face l hl _ (by simp) (by simp)]
        simpa using hτ
      · intro x hx
        simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hx
        obtain ⟨⟨hk, h0, hv⟩, -⟩ := hx
        obtain ⟨⟨v, r⟩, k⟩ := x
        simp only at hk h0 hv ⊢
        subst hk
        have hv' : (⟨0, hN⟩ : Fin N) = v 0 := Fin.ext hv.symm
        rw [hv', Fin.cons_self_tail, decomposeFin_eq r h0]
      · intro τ _
        obtain ⟨u, ρ⟩ := τ
        simp only [Fin.tail_cons, Equiv.apply_symm_apply]
    rw [h1, h2, h3, h4]
    exact ih _ (faceLabel_admissible l hl)

/-- **Sperner-type lemma for the Kuhn triangulation of the cube.** For `0 < N` and an
admissible labelling, some Kuhn simplex of `{0,…,N}^m` is fully labelled. -/
theorem exists_full (hN : 0 < N) {m : ℕ} (l : (Fin m → ℕ) → Fin (m + 1))
    (hl : Admissible N l) : ∃ σ : Simp m N, full l σ := by
  by_contra h
  simp only [not_exists] at h
  have := sperner_parity hN m l hl
  simp only [h, ite_false, Finset.sum_const_zero] at this
  exact zero_ne_one this

end Applied.Topology.Kuhn
