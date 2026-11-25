import Mathlib.Tactic

/-!
# The second-price (Vickrey) auction is truthful

Bidders `i : ι` (a finite type with at least two elements) submit sealed bids `b : ι → ℝ`.
A highest bidder wins the item and pays the highest bid among the *other* bidders; everybody
else pays nothing.

Ties are handled by an arbitrary tie-breaking rule: the winner is `win b`, where
`win : (ι → ℝ) → ι` is any function that always selects a highest bidder
(`IsHighestBidRule win`). All results hold for every such rule, so no particular tie-breaking
convention is built in; `exists_isHighestBidRule` shows that such rules exist.

* `vickrey_truthful`: bidding one's true value is a weakly dominant strategy.
* `vickrey_truthful_utility_nonneg`: a truthful bidder never ends up with negative utility.
-/

open Finset Function

namespace Applied.Economics

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- The highest bid among the bidders other than `i`. -/
noncomputable def maxOtherBid (b : ι → ℝ) (i : ι) : ℝ :=
  (univ.erase i).sup' (by
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨j, mem_erase.2 ⟨hj, mem_univ j⟩⟩) b

/-- A winner-selection rule for a highest-bid auction: the selected bidder always has a
highest bid. Different rules differ only in how they break ties. -/
def IsHighestBidRule (win : (ι → ℝ) → ι) : Prop :=
  ∀ (b : ι → ℝ) (j : ι), b j ≤ b (win b)

/-- Utility of bidder `i` with value `v i` in the second-price auction with winner rule `win`
under the bid profile `b`: the winner gets the item and pays the highest other bid, everyone
else gets utility `0`. -/
noncomputable def vickreyUtility (win : (ι → ℝ) → ι) (v b : ι → ℝ) (i : ι) : ℝ :=
  if win b = i then v i - maxOtherBid b i else 0

/-- The highest other bid does not depend on one's own bid. -/
lemma maxOtherBid_update (b : ι → ℝ) (i : ι) (x : ℝ) :
    maxOtherBid (update b i x) i = maxOtherBid b i := by
  unfold maxOtherBid
  exact sup'_congr _ rfl (fun j hj => update_of_ne (mem_erase.1 hj).1 _ _)

/-- Every bid of another bidder is at most the highest competing bid. -/
lemma le_maxOtherBid (b : ι → ℝ) {i j : ι} (hji : j ≠ i) : b j ≤ maxOtherBid b i :=
  le_sup' b (mem_erase.2 ⟨hji, mem_univ j⟩)

/-- The highest competing bid is at most any bound valid for all other bidders' bids. -/
lemma maxOtherBid_le (b : ι → ℝ) (i : ι) {c : ℝ} (h : ∀ j, j ≠ i → b j ≤ c) :
    maxOtherBid b i ≤ c :=
  sup'_le _ _ (fun j hj => h j (mem_erase.1 hj).1)

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- Highest-bid winner rules exist (for instance: pick any maximiser of the bid profile). -/
theorem exists_isHighestBidRule [Finite ι] [Nonempty ι] :
    ∃ win : (ι → ℝ) → ι, IsHighestBidRule win := by
  have h : ∀ b : ι → ℝ, ∃ w, ∀ j, b j ≤ b w := fun b => Finite.exists_max b
  choose win hwin using h
  exact ⟨win, hwin⟩

/-- **Truthfulness of the second-price auction.** For every tie-breaking rule, every bidder
`i`, every profile `b` of bids (only the others' entries matter) and every alternative bid `x`,
bidding the true value `v i` gives bidder `i` at least as much utility as bidding `x`. -/
theorem vickrey_truthful (win : (ι → ℝ) → ι) (hwin : IsHighestBidRule win) (v b : ι → ℝ)
    (i : ι) (x : ℝ) :
    vickreyUtility win v (update b i x) i ≤ vickreyUtility win v (update b i (v i)) i := by
  unfold vickreyUtility
  rw [maxOtherBid_update, maxOtherBid_update]
  by_cases hT : win (update b i (v i)) = i
  · -- truthful bid wins: every other bid is at most `v i`
    have hle : maxOtherBid b i ≤ v i := by
      refine maxOtherBid_le b i (fun j hj => ?_)
      have := hwin (update b i (v i)) j
      rwa [hT, update_self, update_of_ne hj] at this
    simp only [hT, ↓reduceIte]
    split_ifs <;> linarith
  · -- truthful bid loses: the winner bids at least `v i`
    have hge : v i ≤ maxOtherBid b i := by
      have := hwin (update b i (v i)) i
      rw [update_self, update_of_ne hT] at this
      exact this.trans (le_maxOtherBid b hT)
    simp only [hT, ↓reduceIte]
    split_ifs <;> linarith

/-- A truthful bidder never gets negative utility (individual rationality). -/
theorem vickrey_truthful_utility_nonneg (win : (ι → ℝ) → ι) (hwin : IsHighestBidRule win)
    (v b : ι → ℝ) (i : ι) :
    0 ≤ vickreyUtility win v (update b i (v i)) i := by
  unfold vickreyUtility
  rw [maxOtherBid_update]
  split_ifs with hT
  · have hle : maxOtherBid b i ≤ v i := by
      refine maxOtherBid_le b i (fun j hj => ?_)
      have := hwin (update b i (v i)) j
      rwa [hT, update_self, update_of_ne hj] at this
    linarith
  · exact le_rfl

/-- The second-price auction with `n ≥ 2` bidders indexed by `Fin n` is truthful. -/
theorem vickrey_truthful_fin {n : ℕ} (hn : 2 ≤ n) (win : (Fin n → ℝ) → Fin n)
    (hwin : ∀ (b : Fin n → ℝ) (j : Fin n), b j ≤ b (win b)) (v b : Fin n → ℝ) (i : Fin n)
    (x : ℝ) :
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
    vickreyUtility win v (update b i x) i ≤ vickreyUtility win v (update b i (v i)) i :=
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  vickrey_truthful win hwin v b i x

end Applied.Economics
