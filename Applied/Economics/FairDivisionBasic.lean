import Mathlib.Tactic
import Mathlib.Combinatorics.Colex

/-!
# Fair division of indivisible goods: shared definitions and lemmas

This file collects what the files on EFX and PMMS allocations (`EFX*.lean`, `PMMS.lean`) have
in common. Throughout, agents `i : A` have additive valuations `v i : G → ℝ` over a finite set
`G` of indivisible goods, and a (complete) allocation is a map `a : G → A`: good `g` goes to
agent `a g`, so the bundle of agent `j` is `{h | a h = j}`.

## Main definitions

* `IsEFX v a`: the allocation `a` is *envy-free up to any good* (strong form: the removed good
  may be one the envious agent values at zero).
* `IsPartialAlloc X`, `IsPEFX v X`: the same notions for allocations given as a family of
  pairwise disjoint bundles `X : A → Finset G`, which need not cover all goods.

## Main statements

* Bundle arithmetic: `sum_filter_eq_and_ne_add` (a bundle is the bundle without `g`, plus `g`),
  `sum_filter_and_ne_le` (removing a good does not increase the value),
  `sum_filter_or_eq` (the union of two bundles), `sum_split_two` (two terms taken out of a sum
  over all agents).
* From bundles to allocation maps: `isEFX_of_bundles`, `exists_isEFX_of_isPEFX`.
* Perturbation to a non-degenerate instance: `exists_perturbation`,
  `exists_pos_perturbation`, `exists_pos_nondegenerate`. Any finite family of valuations can
  be replaced by positive valuations under which different sets of goods have different
  values, such that every weak comparison between two sets under the new valuations also holds
  under the old ones. Hence EFX (which is a conjunction of weak comparisons) for the perturbed
  instance gives EFX for the original instance. Used for two types of agents
  (`EFXTwoTypes.lean`) and for three agents (`EFXThree.lean`).

## Not in this file

No existence theorem: those are in `EFX.lean` (identical valuations, two agents) and the files
importing it. The envy-cycle lemma `exists_perm_of_forall_rel` and the restricted notion
`IsEFXOn` are in `EFXOrdered.lean`; the maximin share `mms2` is in `PMMS.lean`.
-/

open Finset Function

namespace Applied.Economics

/-! ### Allocations and EFX -/

section Alloc

variable {A G : Type*} [Fintype G] [DecidableEq A] [DecidableEq G]

/-- The allocation `a` (good `g` goes to agent `a g`) is envy-free up to any good for the
additive valuations `v`: for all agents `i`, `j` and every good `g` in `j`'s bundle, agent `i`
values `j`'s bundle without `g` at most as much as their own bundle. -/
def IsEFX (v : A → G → ℝ) (a : G → A) : Prop :=
  ∀ i j : A, ∀ g : G, a g = j →
    ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h

/-! ### Sums over bundles -/

/-- Removing one good `g` from the bundle `j` that contains it: the value of the rest plus the
value of `g` is the value of the bundle. -/
lemma sum_filter_eq_and_ne_add {M : Type*} [AddCommMonoid M] (f : G → M) (a : G → A) {j : A}
    {g : G} (hg : a g = j) :
    ∑ h with a h = j ∧ h ≠ g, f h + f g = ∑ h with a h = j, f h := by
  have : (univ.filter fun h => a h = j ∧ h ≠ g) = (univ.filter fun h => a h = j).erase g := by
    ext h
    simp [and_comm]
  rw [this, sum_erase_add _ _ (by simp [hg])]

/-- Removing a good from a bundle does not increase its value, for a non-negative valuation
(the good need not belong to the bundle). -/
lemma sum_filter_and_ne_le {f : G → ℝ} (hf : ∀ g, 0 ≤ f g) (a : G → A) (j : A) (g : G) :
    ∑ h with a h = j ∧ h ≠ g, f h ≤ ∑ h with a h = j, f h :=
  sum_le_sum_of_subset_of_nonneg
    (fun h hh => by
      simp only [mem_filter, mem_univ, true_and] at hh ⊢
      exact hh.1)
    (fun h _ _ => hf h)

/-- The union of two distinct bundles has value equal to the sum of their values. -/
lemma sum_filter_or_eq {M : Type*} [AddCommMonoid M] (f : G → M) (a : G → A) {i j : A}
    (hij : i ≠ j) :
    ∑ h with (a h = i ∨ a h = j), f h = ∑ h with a h = i, f h + ∑ h with a h = j, f h := by
  rw [filter_or, sum_union]
  exact disjoint_filter.2 fun h _ h1 h2 => hij (h1 ▸ h2)

omit [Fintype G] [DecidableEq G] in
/-- A sum over all agents, with the terms of two distinct agents `i`, `j` taken out. -/
lemma sum_split_two {M : Type*} [AddCommMonoid M] [Fintype A] (F : A → M) {i j : A}
    (hij : i ≠ j) : ∑ l, F l = F i + F j + ∑ l ∈ (univ.erase i).erase j, F l := by
  rw [← add_sum_erase univ F (mem_univ i),
    ← add_sum_erase (univ.erase i) F (mem_erase.2 ⟨hij.symm, mem_univ j⟩), add_assoc]

end Alloc

/-! ### Allocations given by bundles -/

section Bundles

variable {A G : Type*} [DecidableEq A] [DecidableEq G]

/-- A partial allocation: bundles of different agents are disjoint. -/
def IsPartialAlloc (X : A → Finset G) : Prop :=
  ∀ i j, i ≠ j → Disjoint (X i) (X j)

/-- EFX (strong form) for a partial allocation given by bundles. -/
def IsPEFX (v : A → G → ℝ) (X : A → Finset G) : Prop :=
  ∀ i j, ∀ h ∈ X j, ∑ x ∈ (X j).erase h, v i x ≤ ∑ x ∈ X i, v i x

/-- If the bundles of the allocation map `a` are the sets `X j`, and the family `X` satisfies
the EFX inequalities, then `a` is EFX. -/
lemma isEFX_of_bundles [Fintype G] {v : A → G → ℝ} {a : G → A} {X : A → Finset G}
    (hX : ∀ h j, a h = j ↔ h ∈ X j) (hE : IsPEFX v X) : IsEFX v a := by
  intro i j g hg
  have h1 : (univ.filter fun h => a h = j ∧ h ≠ g) = (X j).erase g := by
    ext h
    simp [hX, and_comm]
  have h2 : (univ.filter fun h => a h = i) = X i := by
    ext h
    simp [hX]
  rw [h1, h2]
  exact hE i j g ((hX g j).1 hg)

/-- A partial EFX allocation that covers all goods gives an EFX allocation map. -/
lemma exists_isEFX_of_isPEFX [Fintype G] {v : A → G → ℝ} {X : A → Finset G}
    (hX : IsPartialAlloc X) (hcov : ∀ g, ∃ i, g ∈ X i) (hE : IsPEFX v X) :
    ∃ a : G → A, IsEFX v a := by
  choose a ha using hcov
  refine ⟨a, isEFX_of_bundles (fun h j => ⟨?_, fun hh => ?_⟩) hE⟩
  · rintro rfl
    exact ha h
  · by_contra hne
    exact disjoint_left.1 (hX _ _ hne) (ha h) hh

end Bundles

/-! ### Perturbation to positive, non-degenerate valuations -/

section Perturbation

variable {A G : Type*}

/-- Perturbation weights: there are positive weights `w` on the goods whose subset sums are
pairwise different, and whose subset-sum differences are smaller than every non-zero
difference of subset sums of any `v i`. (The weights are a small multiple of distinct powers
of two.) -/
lemma exists_perturbation [Fintype A] [Fintype G] (v : A → G → ℝ) :
    ∃ w : G → ℝ, (∀ g, 0 < w g) ∧ (∀ S T : Finset G, ∑ g ∈ S, w g = ∑ g ∈ T, w g → S = T) ∧
      ∀ i (S T : Finset G), ∑ g ∈ S, v i g ≠ ∑ g ∈ T, v i g →
        |∑ g ∈ S, w g - ∑ g ∈ T, w g| < |∑ g ∈ S, v i g - ∑ g ∈ T, v i g| := by
  classical
  set e := Fintype.equivFin G
  set emb : G ↪ ℕ := e.toEmbedding.trans Fin.valEmbedding with hemb
  set b : G → ℝ := fun g => (2 : ℝ) ^ (e g : ℕ) with hb
  have hbsum : ∀ S : Finset G, ∑ g ∈ S, b g = ((∑ k ∈ S.map emb, 2 ^ k : ℕ) : ℝ) := by
    intro S
    rw [sum_map]
    push_cast
    rfl
  have hbinj : ∀ S T : Finset G, ∑ g ∈ S, b g = ∑ g ∈ T, b g → S = T := by
    intro S T h
    rw [hbsum, hbsum] at h
    exact map_injective emb (geomSum_injective le_rfl (Nat.cast_injective h))
  have hb0 : ∀ g, 0 < b g := fun g => pow_pos two_pos _
  set W := ∑ g, b g with hW
  have hW0 : 0 ≤ W := sum_nonneg (fun g _ => (hb0 g).le)
  -- `δ` is a lower bound for all non-zero differences of subset sums of the `v i`
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ i (S T : Finset G), ∑ g ∈ S, v i g ≠ ∑ g ∈ T, v i g →
      δ ≤ |∑ g ∈ S, v i g - ∑ g ∈ T, v i g| := by
    obtain ⟨D, hD⟩ : ∃ D : Finset (A × Finset G × Finset G), D = univ.filter
        (fun p => ∑ g ∈ p.2.1, v p.1 g ≠ ∑ g ∈ p.2.2, v p.1 g) := ⟨_, rfl⟩
    have hmemD : ∀ i (S T : Finset G), ∑ g ∈ S, v i g ≠ ∑ g ∈ T, v i g → (i, S, T) ∈ D :=
      fun i S T h => by rw [hD]; exact mem_filter.2 ⟨mem_univ _, h⟩
    by_cases hDne : D.Nonempty
    · obtain ⟨p, hp, hpmin⟩ := D.exists_min_image
        (fun p => |∑ g ∈ p.2.1, v p.1 g - ∑ g ∈ p.2.2, v p.1 g|) hDne
      have hp' : ∑ g ∈ p.2.1, v p.1 g ≠ ∑ g ∈ p.2.2, v p.1 g := by
        rw [hD] at hp
        exact (mem_filter.1 hp).2
      exact ⟨_, abs_pos.2 (sub_ne_zero.2 hp'), fun i S T h => hpmin _ (hmemD i S T h)⟩
    · exact ⟨1, one_pos, fun i S T h => absurd ⟨_, hmemD i S T h⟩ hDne⟩
  -- scale the powers of two so that all their subset sums lie in `[0, δ)`
  set ε := δ / (W + 1) with hε
  have hε0 : 0 < ε := div_pos hδ (by linarith)
  have hεW : ε * W < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨fun g => ε * b g, fun g => mul_pos hε0 (hb0 g), fun S T h => ?_, fun i S T h => ?_⟩
  · rw [← mul_sum, ← mul_sum] at h
    exact hbinj S T (mul_left_cancel₀ hε0.ne' h)
  · have hle : ∀ S : Finset G, 0 ≤ ∑ g ∈ S, ε * b g ∧ ∑ g ∈ S, ε * b g ≤ ε * W := by
      intro S
      rw [← mul_sum]
      refine ⟨mul_nonneg hε0.le (sum_nonneg (fun g _ => (hb0 g).le)), ?_⟩
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ S)
        (fun g _ _ => (hb0 g).le)) hε0.le
    have h1 := hle S
    have h2 := hle T
    refine lt_of_lt_of_le ?_ (hδle i S T h)
    rw [abs_lt]
    constructor <;> linarith

/-- Perturbation by a common positive weight function: for any valuations `v` there are
positive weights `w` on the goods such that under the valuations `v i + w` every agent values
different sets of goods differently, and every weak comparison of two sets under `v i + w`
also holds under `v i`. All agents are perturbed by the same `w`, so agents with equal
valuations still have equal valuations. -/
lemma exists_pos_perturbation [Fintype A] [Fintype G] (v : A → G → ℝ) :
    ∃ w : G → ℝ, (∀ g, 0 < w g) ∧
      (∀ i (S T : Finset G), S ≠ T → ∑ g ∈ S, (v i g + w g) ≠ ∑ g ∈ T, (v i g + w g)) ∧
      ∀ i (S T : Finset G), ∑ g ∈ S, (v i g + w g) ≤ ∑ g ∈ T, (v i g + w g) →
        ∑ g ∈ S, v i g ≤ ∑ g ∈ T, v i g := by
  obtain ⟨w, hwpos, hwinj, hwlt⟩ := exists_perturbation v
  have hsum' : ∀ i (S : Finset G), ∑ g ∈ S, (v i g + w g) = ∑ g ∈ S, v i g + ∑ g ∈ S, w g :=
    fun i S => sum_add_distrib
  refine ⟨w, hwpos, fun i S T hST h => ?_, fun i S T h => ?_⟩
  · rw [hsum', hsum'] at h
    by_cases hvST : ∑ g ∈ S, v i g = ∑ g ∈ T, v i g
    · exact hST (hwinj S T (by linarith))
    · have := hwlt i S T hvST
      rw [show ∑ g ∈ S, w g - ∑ g ∈ T, w g = -(∑ g ∈ S, v i g - ∑ g ∈ T, v i g) by linarith,
        abs_neg] at this
      exact lt_irrefl _ this
  · by_contra hlt
    push Not at hlt
    have h1 := hwlt i T S hlt.ne
    rw [hsum', hsum'] at h
    rw [abs_of_neg (sub_neg.2 hlt)] at h1
    have h2 := le_abs_self (∑ g ∈ T, w g - ∑ g ∈ S, w g)
    linarith

/-- Perturbation to a non-degenerate instance: for non-negative valuations `v` there are
positive valuations `v'` under which every agent values different sets of goods differently,
and such that every weak comparison of two sets under `v' i` also holds under `v i`. -/
lemma exists_pos_nondegenerate [Fintype A] [Fintype G] (v : A → G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) :
    ∃ v' : A → G → ℝ, (∀ i g, 0 < v' i g) ∧
      (∀ i (S T : Finset G), S ≠ T → ∑ g ∈ S, v' i g ≠ ∑ g ∈ T, v' i g) ∧
      ∀ i (S T : Finset G), ∑ g ∈ S, v' i g ≤ ∑ g ∈ T, v' i g →
        ∑ g ∈ S, v i g ≤ ∑ g ∈ T, v i g := by
  obtain ⟨w, hwpos, hnd, htrans⟩ := exists_pos_perturbation v
  exact ⟨fun i g => v i g + w g, fun i g => by linarith [hv i g, hwpos g], hnd, htrans⟩

end Perturbation

end Applied.Economics
