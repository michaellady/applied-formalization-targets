import Applied.Economics.Minimax

/-!
# The Bondareva–Shapley theorem

A cooperative game with transferable utility on a finite player set `N` is a function
`v : Finset N → ℝ` (as in `Applied/Economics/Shapley.lean`; `v ∅ = 0` is not built in).

* `IsInCore v x`: the payoff vector `x : N → ℝ` is efficient (`∑ i, x i = v univ`) and no
  coalition `S` can improve on it (`v S ≤ ∑ i ∈ S, x i`).
* `IsBalancedWeights w`: `w : Finset N → ℝ` is a non-negative weighting of coalitions such that
  for every player the weights of the coalitions containing that player sum to `1`.
* `IsBalancedGame v`: `∑ S, w S * v S ≤ v univ` for every balanced weighting `w`.
* `core_nonempty_iff_balanced`: **the core is non-empty iff the game is balanced.**

The proof of the hard direction does not use linear-programming duality (which Mathlib lacks
in this form) but von Neumann's minimax theorem for matrix games (`exists_saddle_point`),
applied to the game in which one player picks a coalition `S`, the other a player `i`, and the
payoff is `v S - ∑ j ∈ S, v {j} - D * [i ∈ S]` with `D = v univ - ∑ j, v {j}`.

The empty coalition is allowed to carry weight. For games with `v ∅ = 0` this changes nothing
(`isBalancedGame_iff_of_empty`): the weight of `∅` enters neither the balancedness constraints
nor the sum.
-/

open Finset Matrix

namespace Applied.Economics.Cooperative

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The payoff vector `x` is in the core of the game `v`: it distributes exactly `v univ` and
gives every coalition at least its worth. -/
def IsInCore (v : Finset N → ℝ) (x : N → ℝ) : Prop :=
  ∑ i, x i = v univ ∧ ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i

/-- Balanced weights: non-negative weights on coalitions such that, for every player, the
weights of the coalitions containing the player sum to `1`. -/
def IsBalancedWeights (w : Finset N → ℝ) : Prop :=
  (∀ S, 0 ≤ w S) ∧ ∀ i : N, ∑ S ∈ univ.filter (fun S : Finset N => i ∈ S), w S = 1

/-- The game `v` is balanced: no balanced weighting of coalitions is worth more than the grand
coalition. -/
def IsBalancedGame (v : Finset N → ℝ) : Prop :=
  ∀ w : Finset N → ℝ, IsBalancedWeights w → ∑ S, w S * v S ≤ v univ

/-- Summing a coalition function against weights concentrated on singletons. -/
private lemma sum_singleton_weights (a : N → ℝ) (g : Finset N → ℝ) :
    ∑ S : Finset N, (∑ i, if S = {i} then a i else 0) * g S = ∑ i, a i * g {i} := by
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- Exchanging the order of summation over coalitions and their members. -/
private lemma sum_mul_sum_mem (w : Finset N → ℝ) (x : N → ℝ) :
    ∑ S : Finset N, w S * ∑ i ∈ S, x i = ∑ i, x i * ∑ S : Finset N, if i ∈ S then w S else 0 := by
  have h : ∀ S : Finset N, w S * ∑ i ∈ S, x i = ∑ i, if i ∈ S then x i * w S else 0 := by
    intro S
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs <;> simp

/-- **Bondareva–Shapley, easy direction.** A game with a non-empty core is balanced. -/
theorem IsInCore.isBalancedGame {v : Finset N → ℝ} {x : N → ℝ} (hx : IsInCore v x) :
    IsBalancedGame v := by
  rintro w ⟨hw0, hw1⟩
  calc ∑ S, w S * v S ≤ ∑ S, w S * ∑ i ∈ S, x i :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hx.2 S) (hw0 S)
    _ = ∑ i, x i * ∑ S : Finset N, if i ∈ S then w S else 0 := sum_mul_sum_mem w x
    _ = ∑ i, x i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter, hw1 i, mul_one]
    _ = v univ := hx.1

/-- Homogeneous form of balancedness: if non-negative weights cover every player with total
weight exactly `M ≥ 0`, their worth is at most `M * v univ`. -/
theorem IsBalancedGame.sum_le {v : Finset N → ℝ} (hv : IsBalancedGame v) (w : Finset N → ℝ)
    (hw0 : ∀ S, 0 ≤ w S) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i : N, ∑ S : Finset N, (if i ∈ S then w S else 0) = M) :
    ∑ S, w S * v S ≤ M * v univ := by
  set t : ℝ := 1 / (M + 1) with ht
  have htpos : 0 < t := by positivity
  have htM : 1 - t * M = t := by rw [ht]; field_simp; ring
  have hbal : IsBalancedWeights fun S => t * w S + if S = univ then t else 0 := by
    refine ⟨fun S => ?_, fun i => ?_⟩
    · have := mul_nonneg htpos.le (hw0 S)
      dsimp only
      split_ifs <;> linarith
    · rw [Finset.sum_filter]
      have : ∀ S : Finset N, (if i ∈ S then t * w S + (if S = univ then t else 0) else 0)
          = t * (if i ∈ S then w S else 0) + if S = univ then t else 0 := by
        intro S
        by_cases hS : S = univ
        · subst hS; simp
        · by_cases hi : i ∈ S <;> simp [hS, hi]
      simp_rw [this]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hw i]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      linarith
  have h := hv _ hbal
  simp_rw [add_mul, ite_mul, zero_mul, mul_assoc] at h
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  have h2 : t * ∑ S, w S * v S ≤ t * (M * v univ) := by
    have htM' : t * M = 1 - t := by linarith
    have : t * (M * v univ) = (1 - t) * v univ := by rw [← mul_assoc, htM']
    rw [this]; linarith
  exact le_of_mul_le_mul_left h2 htpos

/-- **Bondareva–Shapley, hard direction.** A balanced game has a non-empty core. -/
theorem IsBalancedGame.exists_isInCore {v : Finset N → ℝ} (hv : IsBalancedGame v) :
    ∃ x, IsInCore v x := by
  rcases isEmpty_or_nonempty N with hN | hN
  · -- no players: the homogeneous form with zero weights and with weight on `∅ = univ`
    have h0 := hv (fun _ => 0) ⟨fun _ => le_rfl, fun i => (hN.false i).elim⟩
    have h1 := hv.sum_le (fun S => if S = univ then 1 else 0)
      (fun S => by split_ifs <;> norm_num) 0 le_rfl (fun i => (hN.false i).elim)
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    simp at h0
    rw [Finset.univ_eq_empty] at h1
    refine ⟨fun _ => 0, by simp; linarith, fun S => ?_⟩
    have hS : S = univ := Subsingleton.elim _ _
    subst hS
    simp; linarith
  · set σ : ℝ := ∑ j, v {j} with hσ
    set D : ℝ := v univ - σ with hD
    set A : Matrix (Finset N) N ℝ :=
      fun S i => v S - ∑ j ∈ S, v {j} - if i ∈ S then D else 0 with hA
    obtain ⟨μ, hμ, q, hq, h1, h2⟩ := exists_saddle_point A
    -- payoff of a pure coalition against `q`
    have hrow : ∀ S : Finset N, gamePayoff A (Pi.single S 1) q
        = v S - ∑ i ∈ S, (v {i} + D * q i) := by
      intro S
      have e : gamePayoff A (Pi.single S 1) q = ∑ i, A S i * q i := by
        simp [gamePayoff, dotProduct, mulVec, Pi.single_apply]
      have e' : ∀ i, A S i * q i
          = (v S - ∑ j ∈ S, v {j}) * q i - if i ∈ S then D * q i else 0 := by
        intro i
        simp only [hA]
        split_ifs <;> ring
      rw [e]
      simp_rw [e']
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hq.2, Finset.sum_ite_mem,
        Finset.univ_inter, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    -- payoff of `μ` against a pure player
    set c : N → ℝ := fun j => ∑ S : Finset N, if j ∈ S then μ S else 0 with hc
    have hc0 : ∀ j, 0 ≤ c j := fun j =>
      Finset.sum_nonneg fun S _ => by split_ifs <;> [exact hμ.1 S; exact le_rfl]
    have hcol : ∀ i : N, gamePayoff A μ (Pi.single i 1)
        = ∑ S, μ S * v S - ∑ j, v {j} * c j - D * c i := by
      intro i
      have e : gamePayoff A μ (Pi.single i 1) = ∑ S, μ S * A S i := by
        simp [gamePayoff, dotProduct, mulVec, Pi.single_apply]
      have e' : ∀ S : Finset N, μ S * A S i
          = μ S * v S - μ S * ∑ j ∈ S, v {j} - D * if i ∈ S then μ S else 0 := by
        intro S
        simp only [hA]
        split_ifs <;> ring
      rw [e]
      simp_rw [e']
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_mul_sum_mem, ← Finset.mul_sum]
    -- the value of the matrix game is at most `0`
    have hval : gamePayoff A μ q ≤ 0 := by
      by_contra hpos
      rw [not_le] at hpos
      obtain ⟨i₀, hi₀⟩ := Finite.exists_max c
      set M := c i₀ with hMdef
      have hbound := hv.sum_le (fun S => μ S + ∑ i, if S = {i} then M - c i else 0)
        (fun S => add_nonneg (hμ.1 S) (Finset.sum_nonneg fun i _ => by
          split_ifs <;> [exact sub_nonneg.mpr (hi₀ i); exact le_rfl])) M (hc0 i₀)
        (fun j => by
          have : ∀ S : Finset N,
              (if j ∈ S then μ S + ∑ i, (if S = {i} then M - c i else 0) else 0)
                = (if j ∈ S then μ S else 0)
                  + (∑ i, if S = {i} then M - c i else 0) * (if j ∈ S then 1 else 0) := by
            intro S; split_ifs <;> simp
          simp_rw [this]
          rw [Finset.sum_add_distrib, sum_singleton_weights]
          simp [hc])
      simp_rw [add_mul] at hbound
      rw [Finset.sum_add_distrib, sum_singleton_weights] at hbound
      simp_rw [sub_mul] at hbound
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hbound
      have h3 := h2 _ (single_mem_mixedStrategies i₀)
      rw [hcol i₀] at h3
      have e : ∑ j, v {j} * c j = ∑ j, c j * v {j} :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [e] at h3
      have hDM : D * c i₀ = M * v univ - M * σ := by rw [hD, ← hMdef]; ring
      rw [← hσ] at hbound
      linarith
    refine ⟨fun i => v {i} + D * q i, ?_, fun S => ?_⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq.2, hD, hσ]; ring
    · have := (h1 _ (single_mem_mixedStrategies S)).trans hval
      rw [hrow S] at this
      linarith

/-- **Bondareva–Shapley theorem.** The core of a finite transferable-utility game is non-empty
if and only if the game is balanced. -/
theorem core_nonempty_iff_balanced (v : Finset N → ℝ) :
    (∃ x, IsInCore v x) ↔ IsBalancedGame v :=
  ⟨fun ⟨_, hx⟩ => hx.isBalancedGame, fun h => h.exists_isInCore⟩

/-- For games with `v ∅ = 0`, balancedness as defined here (weights on all coalitions,
including `∅`) is the same as the textbook condition, which only involves the non-empty
coalitions. -/
theorem isBalancedGame_iff_of_empty (v : Finset N → ℝ) (h0 : v ∅ = 0) :
    IsBalancedGame v ↔ ∀ w : Finset N → ℝ, (∀ S : Finset N, S.Nonempty → 0 ≤ w S) →
      (∀ i : N, ∑ S ∈ univ.filter (fun S : Finset N => i ∈ S), w S = 1) →
      ∑ S ∈ univ.filter (fun S : Finset N => S.Nonempty), w S * v S ≤ v univ := by
  have key : ∀ w : Finset N → ℝ,
      ∑ S ∈ univ.filter (fun S : Finset N => S.Nonempty), w S * v S = ∑ S, w S * v S := by
    intro w
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs with hS
    · rfl
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS, h0, mul_zero]
  constructor
  · intro hv w hw0 hw1
    have hbal : IsBalancedWeights fun S : Finset N => if S.Nonempty then w S else 0 := by
      refine ⟨fun S => ?_, fun i => ?_⟩
      · dsimp only
        split_ifs with hS
        · exact hw0 S hS
        · exact le_rfl
      · rw [← hw1 i]
        refine Finset.sum_congr rfl fun S hS => ?_
        have hne : S.Nonempty := ⟨i, (Finset.mem_filter.mp hS).2⟩
        simp [hne]
    have := hv _ hbal
    rw [← key] at this
    refine le_of_eq_of_le (Finset.sum_congr rfl fun S hS => ?_) this
    have hne : S.Nonempty := (Finset.mem_filter.mp hS).2
    simp [hne]
  · intro h w hw
    rw [← key]
    exact h w (fun S _ => hw.1 S) hw.2

end Applied.Economics.Cooperative
