import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# The Shapley value of a finite cooperative game

A cooperative game with transferable utility on a finite player set `N` is a function
`v : Finset N → ℝ` giving the worth of every coalition. (The usual normalisation `v ∅ = 0` is
not built in; it appears as a hypothesis where needed.)

The Shapley value is defined by random arrival orders: an ordering of the players is a
bijection `σ : N ≃ Fin (Fintype.card N)`; player `i` receives the average, over all
orderings, of the marginal contribution `v (P ∪ {i}) - v P` to the set `P` of players who
arrive before `i`.

* `shapley v i`: the Shapley value of player `i`.
* `shapley_efficient`: the values sum to `v univ - v ∅` (so to `v univ` when `v ∅ = 0`).
* `shapley_symmetric`: interchangeable players get the same value.
* `shapley_null`: a null player gets zero.
* `shapley_add`, `shapley_smul`: the value is additive, and homogeneous, in the game.
-/

open Finset

namespace Applied.Economics.Shapley

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The players arriving strictly before `i` in the ordering `σ`. -/
def predecessors (σ : N ≃ Fin (Fintype.card N)) (i : N) : Finset N :=
  Finset.univ.filter fun j => σ j < σ i

/-- Marginal contribution of player `i` to the coalition of its predecessors in `σ`. -/
def marginal (v : Finset N → ℝ) (σ : N ≃ Fin (Fintype.card N)) (i : N) : ℝ :=
  v (insert i (predecessors σ i)) - v (predecessors σ i)

/-- The **Shapley value** of player `i` in the game `v`: the average marginal contribution of
`i` over all orderings of the players. -/
noncomputable def shapley (v : Finset N → ℝ) (i : N) : ℝ :=
  (∑ σ : N ≃ Fin (Fintype.card N), marginal v σ i) / (Fintype.card N).factorial

/-- Player `i` is a null player: joining never changes the worth of a coalition. -/
def IsNull (v : Finset N → ℝ) (i : N) : Prop := ∀ S : Finset N, i ∉ S → v (insert i S) = v S

/-- Players `i` and `j` are interchangeable: they contribute the same to every coalition
containing neither. -/
def Interchangeable (v : Finset N → ℝ) (i j : N) : Prop :=
  ∀ S : Finset N, i ∉ S → j ∉ S → v (insert i S) = v (insert j S)

omit [DecidableEq N] in
lemma notMem_predecessors (σ : N ≃ Fin (Fintype.card N)) (i : N) : i ∉ predecessors σ i := by
  simp [predecessors]

/-- There are `(card N)!` orderings. -/
lemma card_orderings : Fintype.card (N ≃ Fin (Fintype.card N)) = (Fintype.card N).factorial :=
  Fintype.card_equiv (Fintype.equivFin N)

/-- Along one ordering the marginal contributions telescope. -/
lemma sum_marginal (v : Finset N → ℝ) (σ : N ≃ Fin (Fintype.card N)) :
    ∑ i, marginal v σ i = v Finset.univ - v ∅ := by
  set T : ℕ → Finset N := fun m => Finset.univ.filter fun j => (σ j : ℕ) < m with hT
  have h1 : ∀ i, marginal v σ i = v (T ((σ i : ℕ) + 1)) - v (T (σ i)) := by
    intro i
    have e1 : predecessors σ i = T (σ i) := by
      ext j; simp [predecessors, hT]
    have e2 : insert i (predecessors σ i) = T ((σ i : ℕ) + 1) := by
      ext j
      simp only [predecessors, hT, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
        true_and, Fin.lt_def, Nat.lt_succ_iff_lt_or_eq]
      rw [or_comm]
      refine or_congr Iff.rfl ⟨fun h => by rw [h], fun h => σ.injective (Fin.ext h)⟩
    rw [marginal, e2, e1]
  simp only [h1]
  rw [← Equiv.sum_comp σ.symm]
  simp only [Equiv.apply_symm_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => v (T (k + 1)) - v (T k)) (Fintype.card N),
    Finset.sum_range_sub (fun k => v (T k))]
  have e0 : T 0 = ∅ := by simp [hT]
  have en : T (Fintype.card N) = Finset.univ := by
    ext j; simp [hT]
  rw [e0, en]

/-- **Efficiency.** The Shapley values of all players sum to the worth of the grand coalition
minus the worth of the empty coalition. -/
theorem shapley_efficient (v : Finset N → ℝ) : ∑ i, shapley v i = v Finset.univ - v ∅ := by
  simp only [shapley]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [sum_marginal, Finset.sum_const, Finset.card_univ, card_orderings, nsmul_eq_mul]
  have : ((Fintype.card N).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Efficiency** for games normalised by `v ∅ = 0`. -/
theorem shapley_efficient' (v : Finset N → ℝ) (h0 : v ∅ = 0) :
    ∑ i, shapley v i = v Finset.univ := by
  rw [shapley_efficient, h0, sub_zero]

/-- **Null-player property.** A null player has Shapley value zero. -/
theorem shapley_null (v : Finset N → ℝ) (i : N) (h : IsNull v i) : shapley v i = 0 := by
  simp [shapley, marginal, h _ (notMem_predecessors _ i)]

/-- **Additivity.** The Shapley value of a sum of games is the sum of the Shapley values. -/
theorem shapley_add (v w : Finset N → ℝ) (i : N) :
    shapley (v + w) i = shapley v i + shapley w i := by
  simp only [shapley, marginal, Pi.add_apply]
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- **Homogeneity.** Scaling the game scales the Shapley value. -/
theorem shapley_smul (c : ℝ) (v : Finset N → ℝ) (i : N) :
    shapley (c • v) i = c * shapley v i := by
  simp only [shapley, marginal, Pi.smul_apply, smul_eq_mul]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => by ring

omit [Fintype N] in
lemma mem_image_swap (i j k : N) (S : Finset N) :
    k ∈ S.image (Equiv.swap i j) ↔ Equiv.swap i j k ∈ S := by
  constructor
  · intro hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    simpa using ha
  · intro h
    exact Finset.mem_image.mpr ⟨_, h, by simp⟩

omit [Fintype N] in
/-- Exchanging two interchangeable players does not change the worth of a coalition. -/
lemma Interchangeable.image_swap {v : Finset N → ℝ} {i j : N} (h : Interchangeable v i j)
    (S : Finset N) : v (S.image (Equiv.swap i j)) = v S := by
  by_cases hij : i = j
  · subst hij; simp
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · congr 1
    ext k
    rw [mem_image_swap]
    by_cases hki : k = i
    · subst hki; simpa using ⟨fun _ => hi, fun _ => hj⟩
    by_cases hkj : k = j
    · subst hkj; simpa using ⟨fun _ => hj, fun _ => hi⟩
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  · have e1 : S.image (Equiv.swap i j) = insert j (S.erase i) := by
      ext k
      rw [mem_image_swap]
      by_cases hki : k = i
      · subst hki; simp [hj, hij]
      by_cases hkj : k = j
      · subst hkj; simp [hi]
      rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      simp [hki, hkj]
    have e2 : S = insert i (S.erase i) := (Finset.insert_erase hi).symm
    rw [e1]
    conv_rhs => rw [e2]
    exact (h _ (Finset.notMem_erase i S) (fun hmem => hj (Finset.mem_of_mem_erase hmem))).symm
  · have e1 : S.image (Equiv.swap i j) = insert i (S.erase j) := by
      ext k
      rw [mem_image_swap]
      by_cases hki : k = i
      · subst hki; simp [hj]
      by_cases hkj : k = j
      · subst hkj; simp [hi, Ne.symm hij]
      rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      simp [hki, hkj]
    have e2 : S = insert j (S.erase j) := (Finset.insert_erase hj).symm
    rw [e1]
    conv_rhs => rw [e2]
    exact h _ (fun hmem => hi (Finset.mem_of_mem_erase hmem)) (Finset.notMem_erase j S)
  · congr 1
    ext k
    rw [mem_image_swap]
    by_cases hki : k = i
    · subst hki; simpa using ⟨fun hh => absurd hh hj, fun hh => absurd hh hi⟩
    by_cases hkj : k = j
    · subst hkj; simpa using ⟨fun hh => absurd hh hi, fun hh => absurd hh hj⟩
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- **Symmetry.** Interchangeable players have the same Shapley value. -/
theorem shapley_symmetric (v : Finset N → ℝ) (i j : N) (h : Interchangeable v i j) :
    shapley v i = shapley v j := by
  simp only [shapley]
  congr 1
  refine Fintype.sum_bijective (fun σ => (Equiv.swap i j).trans σ) ?_ _ _ fun σ => ?_
  · refine Function.Involutive.bijective fun σ => ?_
    ext k; simp
  · have e1 : predecessors ((Equiv.swap i j).trans σ) j =
        (predecessors σ i).image (Equiv.swap i j) := by
      ext k
      rw [mem_image_swap]
      simp [predecessors]
    have e2 : insert j (predecessors ((Equiv.swap i j).trans σ) j) =
        (insert i (predecessors σ i)).image (Equiv.swap i j) := by
      rw [Finset.image_insert, e1]; simp
    rw [marginal, marginal, e2, e1, h.image_swap, h.image_swap]

/-! ### Uniqueness -/

/-- Shapley's axioms for a value `ψ` (an assignment of a payoff vector to every game),
required only on games normalised by `v ∅ = 0`: efficiency, symmetry, the null-player property
and additivity. -/
structure IsShapleyValue (ψ : (Finset N → ℝ) → N → ℝ) : Prop where
  efficient : ∀ v, v ∅ = 0 → ∑ i, ψ v i = v Finset.univ
  symmetric : ∀ v i j, v ∅ = 0 → Interchangeable v i j → ψ v i = ψ v j
  null : ∀ v i, v ∅ = 0 → IsNull v i → ψ v i = 0
  add : ∀ v w, v ∅ = 0 → w ∅ = 0 → ψ (v + w) = ψ v + ψ w

/-- The Shapley value satisfies Shapley's axioms. -/
theorem shapley_isShapleyValue : IsShapleyValue (shapley (N := N)) where
  efficient v h0 := shapley_efficient' v h0
  symmetric v i j _ h := shapley_symmetric v i j h
  null v i _ h := shapley_null v i h
  add v w _ _ := funext fun i => shapley_add v w i

/-- The unanimity game of the coalition `T`: a coalition is worth `1` if it contains `T` and
`0` otherwise. -/
def unanimity (T : Finset N) : Finset N → ℝ := fun S => if T ⊆ S then 1 else 0

omit [Fintype N] in
lemma unanimity_empty {T : Finset N} (hT : T.Nonempty) : unanimity T ∅ = 0 := by
  simp [unanimity, Finset.subset_empty, hT.ne_empty]

/-- Shapley's axioms determine the value of every multiple of a unanimity game. -/
lemma IsShapleyValue.apply_smul_unanimity {ψ : (Finset N → ℝ) → N → ℝ} (hψ : IsShapleyValue ψ)
    {T : Finset N} (hT : T.Nonempty) (c : ℝ) (i : N) :
    ψ (c • unanimity T) i = if i ∈ T then c / T.card else 0 := by
  have h0 : (c • unanimity T) ∅ = 0 := by simp [unanimity_empty hT]
  have hnull : ∀ k, k ∉ T → ψ (c • unanimity T) k = 0 := by
    intro k hk
    refine hψ.null _ k h0 fun S _ => ?_
    simp [unanimity, Finset.subset_insert_iff_of_notMem hk]
  have hsym : ∀ k ∈ T, ψ (c • unanimity T) k = ψ (c • unanimity T) i ∨ i ∉ T := by
    intro k hk
    by_cases hi : i ∈ T
    · left
      by_cases hki : k = i
      · rw [hki]
      refine hψ.symmetric _ k i h0 fun S hkS hiS => ?_
      have h1 : ¬ T ⊆ insert k S := fun hsub => by
        rcases Finset.mem_insert.mp (hsub hi) with h | h
        · exact hki h.symm
        · exact hiS h
      have h2 : ¬ T ⊆ insert i S := fun hsub => by
        rcases Finset.mem_insert.mp (hsub hk) with h | h
        · exact hki h
        · exact hkS h
      simp [unanimity, h1, h2]
    · exact Or.inr hi
  split_ifs with hi
  · have heff := hψ.efficient _ h0
    have hsplit : ∑ k, ψ (c • unanimity T) k = ∑ k ∈ T, ψ (c • unanimity T) k := by
      symm
      exact Finset.sum_subset (Finset.subset_univ T) fun k _ hk => hnull k hk
    rw [hsplit, Finset.sum_congr rfl fun k hk => (hsym k hk).resolve_right (not_not.mpr hi),
      Finset.sum_const, nsmul_eq_mul] at heff
    have hcard : (T.card : ℝ) ≠ 0 := by
      exact_mod_cast hT.card_pos.ne'
    simp only [Pi.smul_apply, unanimity, Finset.subset_univ, ite_true, smul_eq_mul,
      mul_one] at heff
    rw [eq_div_iff hcard]
    linarith
  · exact hnull i hi

/-- **Uniqueness of the Shapley value.** A value satisfying efficiency, symmetry, the
null-player property and additivity (on games with `v ∅ = 0`) coincides with the Shapley value
on every game with `v ∅ = 0`. -/
theorem IsShapleyValue.eq_shapley {ψ : (Finset N → ℝ) → N → ℝ} (hψ : IsShapleyValue ψ)
    (v : Finset N → ℝ) (h0 : v ∅ = 0) : ψ v = shapley v := by
  classical
  -- induction on the size of the upward closure of the support of `v`
  suffices H : ∀ (k : ℕ) (v : Finset N → ℝ), v ∅ = 0 →
      (Finset.univ.filter fun T : Finset N => ∃ S ⊆ T, v S ≠ 0).card = k →
      ψ v = shapley v from H _ v h0 rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro v h0 hk
    by_cases hsupp : ∃ S, v S ≠ 0
    · obtain ⟨S₀, hS₀⟩ := hsupp
      obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter fun S : Finset N => v S ≠ 0) Finset.card ⟨S₀, by simpa using hS₀⟩
      have hvS : v S ≠ 0 := (Finset.mem_filter.mp hS).2
      have hSne : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        exact hvS h0
      set v' : Finset N → ℝ := v - v S • unanimity S with hv'
      have hv'0 : v' ∅ = 0 := by simp [hv', h0, unanimity_empty hSne]
      have hu0 : (v S • unanimity S) ∅ = 0 := by simp [unanimity_empty hSne]
      have hdecomp : v = v' + v S • unanimity S := by simp [hv']
      have hlt : (Finset.univ.filter fun T : Finset N => ∃ S' ⊆ T, v' S' ≠ 0).card < k := by
        rw [← hk]
        refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨S, ?_, ?_⟩)
        · intro T hT
          obtain ⟨S', hS'T, hS'⟩ := (Finset.mem_filter.mp hT).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          by_cases hvS' : v S' = 0
          · have hsub : S ⊆ S' := by
              by_contra hns
              apply hS'
              simp [hv', unanimity, hns, hvS']
            exact ⟨S, hsub.trans hS'T, hvS⟩
          · exact ⟨S', hS'T, hvS'⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S, Finset.Subset.refl S, hvS⟩
        · intro hmem
          obtain ⟨S', hS'S, hS'⟩ := (Finset.mem_filter.mp hmem).2
          apply hS'
          rcases hS'S.eq_or_ssubset with rfl | hss
          · simp [hv', unanimity]
          · have hvS' : v S' = 0 := by
              by_contra hne
              have := hmin S' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
              exact absurd (Finset.card_lt_card hss) (not_lt.mpr this)
            have hns : ¬ S ⊆ S' := fun h => hss.2 h
            simp [hv', unanimity, hns, hvS']
      have e1 := ih _ hlt v' hv'0 rfl
      have e2 : ψ (v S • unanimity S) = shapley (v S • unanimity S) := by
        funext i
        rw [hψ.apply_smul_unanimity hSne, shapley_isShapleyValue.apply_smul_unanimity hSne]
      rw [hdecomp, hψ.add _ _ hv'0 hu0, shapley_isShapleyValue.add _ _ hv'0 hu0, e1, e2]
    · have hv : v = 0 := by
        funext S
        by_contra hne
        exact hsupp ⟨S, hne⟩
      subst hv
      have z1 := hψ.add 0 0 rfl rfl
      have z2 := shapley_isShapleyValue.add (N := N) 0 0 rfl rfl
      rw [add_zero] at z1 z2
      have z1' : ψ 0 = 0 := by simpa using z1
      have z2' : shapley (0 : Finset N → ℝ) = 0 := by simpa using z2
      rw [z1', z2']

end Applied.Economics.Shapley
