import Applied.Economics.Nash
import Applied.Topology.Brouwer

/-!
# Nash's existence theorem

Every finite game in strategic form has a mixed Nash equilibrium
(`exists_isMixedNash`). The proof is Nash's 1951 argument: the map
`σ i a ↦ (σ i a + gain⁺ i a) / (1 + ∑ b, gain⁺ i b)`, where `gain⁺ i a` is the positive part of
what player `i` would gain by switching to the pure strategy `a`, is a continuous self-map of
the product of the players' simplices of mixed strategies; by Brouwer's fixed point theorem
(`Applied.Topology.brouwer_pi_probSimplex`) it has a fixed point, and its fixed points are
exactly the mixed Nash equilibria (we prove the direction needed).
-/

namespace Applied.Economics

open Finset

section NashExistence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]

omit [∀ i, Fintype (S i)] in
/-- The probability of the pure profile `s` under a product of mixed strategies in which player
`i`'s strategy is replaced by `τ`: the factor of player `i` is `τ (s i)`. -/
lemma prod_update_eq (σ : ∀ j, S j → ℝ) (i : ι) (τ : S i → ℝ) (s : ∀ j, S j) :
    ∏ j, Function.update σ i τ j (s j) = τ (s i) * ∏ j ∈ univ.erase i, σ j (s j) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (ne_of_mem_erase hj)]

/-- The expected payoff is linear in each player's mixed strategy. -/
lemma mixedPayoff_update_eq_sum [∀ i, DecidableEq (S i)] (u : ι → (∀ j, S j) → ℝ)
    (σ : ∀ j, S j → ℝ) (i : ι) (τ : S i → ℝ) (k : ι) :
    mixedPayoff u (Function.update σ i τ) k =
      ∑ a, τ a * mixedPayoff u (Function.update σ i (Pi.single a 1)) k := by
  simp only [mixedPayoff, prod_update_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hsingle : ∑ a, τ a * (Pi.single a (1 : ℝ) : S i → ℝ) (s i) = τ (s i) := by
    simp [Pi.single_apply]
  calc τ (s i) * (∏ j ∈ univ.erase i, σ j (s j)) * u k s
      = (∑ a, τ a * (Pi.single a (1 : ℝ) : S i → ℝ) (s i)) *
          ((∏ j ∈ univ.erase i, σ j (s j)) * u k s) := by rw [hsingle]; ring
    _ = ∑ a, τ a * ((Pi.single a (1 : ℝ) : S i → ℝ) (s i) *
          (∏ j ∈ univ.erase i, σ j (s j)) * u k s) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring

/-- The expected payoff of player `k` is continuous in the profile of mixed strategies. -/
lemma continuous_mixedPayoff (u : ι → (∀ j, S j) → ℝ) (k : ι) :
    Continuous fun σ : (∀ j, S j → ℝ) => mixedPayoff u σ k := by
  unfold mixedPayoff
  exact continuous_finsetSum _ fun s _ =>
    (continuous_finsetProd _ fun j _ => (continuous_apply (s j)).comp (continuous_apply j)).mul
      continuous_const

variable [∀ i, DecidableEq (S i)] (u : ι → (∀ j, S j) → ℝ)

/-- Positive part of the gain of player `i` from switching to the pure strategy `a`. -/
noncomputable def pureGain (σ : ∀ j, S j → ℝ) (i : ι) (a : S i) : ℝ :=
  max 0 (mixedPayoff u (Function.update σ i (Pi.single a 1)) i - mixedPayoff u σ i)

/-- Nash's map: every player shifts probability towards the pure strategies that would improve
their payoff, `σ i a ↦ (σ i a + gain i a) / (1 + ∑ b, gain i b)`. Its fixed points are exactly
the Nash equilibria. -/
noncomputable def nashMap (σ : ∀ j, S j → ℝ) : ∀ j, S j → ℝ :=
  fun i a => (σ i a + pureGain u σ i a) / (1 + ∑ b, pureGain u σ i b)

/-- The gain `pureGain u σ i a` (positive part of the improvement of player `i` from deviating to
the pure strategy `a`) is non-negative. -/
lemma pureGain_nonneg (σ : ∀ j, S j → ℝ) (i : ι) (a : S i) : 0 ≤ pureGain u σ i a :=
  le_max_left _ _

/-- The gain from a pure deviation is continuous in the profile of mixed strategies. -/
lemma continuous_pureGain (i : ι) (a : S i) : Continuous fun σ => pureGain u σ i a := by
  unfold pureGain
  exact continuous_const.max
    (((continuous_mixedPayoff u i).comp (continuous_id.update i continuous_const)).sub
      (continuous_mixedPayoff u i))

/-- Nash's map sends profiles of mixed strategies to profiles of mixed strategies. -/
lemma nashMap_mem (σ : ∀ j, S j → ℝ) (hσ : ∀ i, σ i ∈ mixedStrategies (S i)) (i : ι) :
    nashMap u σ i ∈ mixedStrategies (S i) := by
  have hG : 0 < 1 + ∑ b, pureGain u σ i b :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun b _ => pureGain_nonneg u σ i b)
  refine ⟨fun a => div_nonneg (add_nonneg ((hσ i).1 a) (pureGain_nonneg u σ i a)) hG.le, ?_⟩
  simp only [nashMap]
  rw [← Finset.sum_div, Finset.sum_add_distrib, (hσ i).2, div_self hG.ne']

/-- A fixed point of Nash's map is a mixed Nash equilibrium. -/
theorem isMixedNash_of_nashMap_eq (σ : ∀ j, S j → ℝ) (hσ : ∀ i, σ i ∈ mixedStrategies (S i))
    (hfix : nashMap u σ = σ) : IsMixedNash u σ := by
  refine ⟨hσ, fun i τ hτ => ?_⟩
  set U := mixedPayoff u σ i with hU
  set v : S i → ℝ := fun a => mixedPayoff u (Function.update σ i (Pi.single a 1)) i with hv
  have hUsum : U = ∑ a, σ i a * v a := by
    rw [hU, hv]
    conv_lhs => rw [← Function.update_eq_self i σ]
    exact mixedPayoff_update_eq_sum u σ i (σ i) i
  set G := ∑ b, pureGain u σ i b with hGdef
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun b _ => pureGain_nonneg u σ i b
  -- fixed point equation: σ i a * G = gain a
  have hfixa : ∀ a, σ i a * G = pureGain u σ i a := by
    intro a
    have h := congrFun (congrFun hfix i) a
    simp only [nashMap] at h
    have hpos : (0 : ℝ) < 1 + G := by linarith
    rw [div_eq_iff hpos.ne'] at h
    linarith
  -- some strategy in the support does not beat the mixed payoff
  have hex : ∃ a, 0 < σ i a ∧ v a ≤ U := by
    by_contra hne
    push Not at hne
    have hlt : ∑ a, σ i a * U < ∑ a, σ i a * v a := by
      obtain ⟨a0, ha0⟩ : ∃ a, 0 < σ i a := by
        by_contra h0
        push Not at h0
        have : ∑ a, σ i a ≤ 0 := Finset.sum_nonpos fun a _ => h0 a
        rw [(hσ i).2] at this
        linarith
      apply Finset.sum_lt_sum
      · intro a _
        rcases ((hσ i).1 a).lt_or_eq with h | h
        · exact (mul_lt_mul_of_pos_left (hne a h) h).le
        · rw [← h]; simp
      · exact ⟨a0, mem_univ _, mul_lt_mul_of_pos_left (hne a0 ha0) ha0⟩
    rw [← Finset.sum_mul, (hσ i).2, one_mul, ← hUsum] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨a, ha, hva⟩ := hex
  have hga : pureGain u σ i a = 0 := by
    unfold pureGain
    exact max_eq_left (by simp only [hv] at hva; linarith)
  have hGz : G = 0 := by
    have := hfixa a
    rw [hga] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ha.ne'
    · exact h
  have hgall : ∀ b, v b ≤ U := by
    intro b
    have hb : pureGain u σ i b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => pureGain_nonneg u σ i b).1 hGz b (mem_univ b)
    unfold pureGain at hb
    have := le_max_right (0 : ℝ) (mixedPayoff u (Function.update σ i (Pi.single b 1)) i -
      mixedPayoff u σ i)
    rw [hb] at this
    simp only [hv]
    linarith
  rw [mixedPayoff_update_eq_sum u σ i τ i]
  calc ∑ a, τ a * v a ≤ ∑ a, τ a * U :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hgall b) (hτ.1 b)
    _ = U := by rw [← Finset.sum_mul, hτ.2, one_mul]

/-- **Nash's theorem.** Every finite game (finitely many players, each with a finite non-empty
set of pure strategies) has a mixed Nash equilibrium. -/
theorem exists_isMixedNash [∀ i, Nonempty (S i)] : ∃ σ : ∀ j, S j → ℝ, IsMixedNash u σ := by
  let X := ∀ i, Applied.Topology.probSimplex (S i)
  let V : X → (∀ j, S j → ℝ) := fun x j => (x j).1
  have hV : Continuous V := continuous_pi fun j => continuous_subtype_val.comp (continuous_apply j)
  let F : X → X := fun x i => ⟨nashMap u (V x) i, nashMap_mem u (V x) (fun j => (x j).2) i⟩
  have hF : Continuous F := by
    refine continuous_pi fun i => Continuous.subtype_mk (continuous_pi fun a => ?_) _
    have hden : ∀ x : X, (1 + ∑ b, pureGain u (V x) i b) ≠ 0 := fun x =>
      (add_pos_of_pos_of_nonneg one_pos
        (Finset.sum_nonneg fun b _ => pureGain_nonneg u (V x) i b)).ne'
    exact (((continuous_apply a).comp ((continuous_apply i).comp hV)).add
      ((continuous_pureGain u i a).comp hV)).div
      (continuous_const.add (continuous_finsetSum _ fun b _ =>
        (continuous_pureGain u i b).comp hV)) hden
  obtain ⟨x, hx⟩ := Applied.Topology.brouwer_pi_probSimplex F hF
  refine ⟨V x, isMixedNash_of_nashMap_eq u (V x) (fun j => (x j).2) ?_⟩
  funext i a
  have := congrArg (fun y : X => (y i).1 a) hx
  exact this

end NashExistence

end Applied.Economics
