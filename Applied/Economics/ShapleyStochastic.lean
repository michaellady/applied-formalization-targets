import Applied.Economics.MatrixValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Shapley's theorem: discounted two-player zero-sum stochastic games

A finite two-player zero-sum stochastic game (`ZeroSumStochasticGame S m n`) has a finite set
of states `S`, finite action sets `m` (player 1, the maximiser) and `n` (player 2, the
minimiser), stage payoffs `payoff s a b` (paid by player 2 to player 1) and transition
probabilities `trans s a b s'`.

A behaviour strategy (`Strategy`) chooses a mixed action as a function of the whole history
(list of past states and action pairs) and the current state; a stationary strategy depends on
the current state only. `stageSum G β σ τ k h s` is the expected `β`-discounted sum of the next
`k` stage payoffs, defined by recursion on `k` (finite sums only). `discountedPayoff` is its
limit as `k → ∞` from the empty history, which exists for `0 ≤ β < 1` (`tendsto_stageSum`).

Results:
* `shapleyOp_contracting`: for `0 ≤ β < 1` the Shapley operator
  `(T v)(s) = val[payoff s a b + β ∑ s', trans s a b s' * v s']` is a `β`-contraction for the
  sup norm (because the matrix value is 1-Lipschitz).
* `stationary_guarantee_ge` / `stationary_guarantee_le`: if a stationary strategy of player 1
  guarantees at least `v s` in each one-shot game `[payoff + β ∑ trans * v]`, it guarantees
  at least `v s` in the discounted game against every behaviour strategy (and symmetrically).
* `shapley_theorem`: **Shapley (1953)**: the discounted game has a value vector, the unique
  fixed point of `T`, and both players have stationary optimal strategies.
* `uniform_value_of_acoe`: undiscounted (`n`-stage average) criterion: if `(g, w)` solves the
  average-payoff optimality equation with stationary strategies attaining it, then `g` is the
  uniform value and the stationary strategies are uniformly `ε`-optimal.
* `uniform_value_of_const_value`: in particular, if every state's stage matrix has the same
  value `g` (for example a repeated matrix game, with one state), then `g` is the uniform
  value, whatever the transitions.
-/

open Finset Filter Topology

namespace Applied.Economics

/-- A finite two-player zero-sum stochastic game. Player 1 chooses `a : m`, player 2 chooses
`b : n`; player 1 receives `payoff s a b` from player 2 and the next state is `s'` with
probability `trans s a b s'`. -/
structure ZeroSumStochasticGame (S m n : Type*) [Fintype S] where
  payoff : S → m → n → ℝ
  trans : S → m → n → S → ℝ
  trans_nonneg : ∀ s a b s', 0 ≤ trans s a b s'
  trans_sum : ∀ s a b, ∑ s', trans s a b s' = 1

namespace ZeroSumStochasticGame

variable {S m n : Type*} [Fintype S] [Fintype m] [Fintype n]

/-- A history: past states and action pairs, in chronological order. -/
abbrev History (S m n : Type*) := List (S × m × n)

/-- A behaviour strategy with action set `k`: a mixed action for every history and current
state. -/
structure Strategy (H S k : Type*) [Fintype k] where
  prob : H → S → k → ℝ
  mem : ∀ h s, prob h s ∈ mixedStrategies k

/-- The stationary strategy playing the mixed action `x s` in state `s`, whatever the history. -/
def Strategy.stationary {H S k : Type*} [Fintype k] (x : S → k → ℝ)
    (hx : ∀ s, x s ∈ mixedStrategies k) : Strategy H S k :=
  ⟨fun _ s => x s, fun _ s => hx s⟩

variable (G : ZeroSumStochasticGame S m n)

/-- The one-shot game in state `s` with continuation values `v` and discount factor `β`. -/
def stageMatrix (β : ℝ) (v : S → ℝ) (s : S) : Matrix m n ℝ :=
  fun a b => G.payoff s a b + β * ∑ s', G.trans s a b s' * v s'

/-- `stageSum G β σ τ k h s`: expected `β`-discounted sum of the next `k` stage payoffs
(`∑_{t<k} β^t r_t`), after history `h` in current state `s`, when player 1 plays `σ` and
player 2 plays `τ`. With `β = 1` it is the undiscounted `k`-stage total. -/
noncomputable def stageSum (β : ℝ) (σ : Strategy (History S m n) S m)
    (τ : Strategy (History S m n) S n) : ℕ → History S m n → S → ℝ
  | 0, _, _ => 0
  | k + 1, h, s => gamePayoff (fun a b => G.payoff s a b +
      β * ∑ s', G.trans s a b s' * stageSum β σ τ k (h ++ [(s, a, b)]) s')
      (σ.prob h s) (τ.prob h s)

lemma stageSum_zero (β : ℝ) (σ : Strategy (History S m n) S m)
    (τ : Strategy (History S m n) S n) (h : History S m n) (s : S) :
    G.stageSum β σ τ 0 h s = 0 := rfl

omit [Fintype m] [Fintype n] in
/-- Averaging against a probability vector preserves `u ≤ w + c`. -/
lemma sum_trans_le {u w : S → ℝ} {c : ℝ} (huw : ∀ s', u s' ≤ w s' + c) (s : S) (a : m) (b : n) :
    ∑ s', G.trans s a b s' * u s' ≤ ∑ s', G.trans s a b s' * w s' + c := by
  calc ∑ s', G.trans s a b s' * u s' ≤ ∑ s', G.trans s a b s' * (w s' + c) :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (huw s') (G.trans_nonneg s a b s')
    _ = ∑ s', G.trans s a b s' * w s' + c := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, G.trans_sum, one_mul]

/-! ### The Shapley operator is a contraction -/

section Shapley

variable [Nonempty m] [Nonempty n]

/-- The Shapley operator: `(T v)(s)` is the value of the one-shot game `stageMatrix β v s`. -/
noncomputable def shapleyOp (β : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => matrixValue (G.stageMatrix β v s)

/-- For `0 ≤ β`, `dist (T v) (T w) ≤ β * dist v w` in the sup metric. -/
theorem dist_shapleyOp_le {β : ℝ} (hβ : 0 ≤ β) (v w : S → ℝ) :
    dist (G.shapleyOp β v) (G.shapleyOp β w) ≤ β * dist v w := by
  rw [dist_pi_le_iff (mul_nonneg hβ dist_nonneg)]
  intro s
  rw [Real.dist_eq]
  apply abs_matrixValue_sub_le
  intro a b
  have hvw : ∀ s', |v s' - w s'| ≤ dist v w := fun s' => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist v w s'
  have h1 := G.sum_trans_le (u := v) (w := w) (c := dist v w)
    (fun s' => by linarith [(abs_le.1 (hvw s')).2]) s a b
  have h2 := G.sum_trans_le (u := w) (w := v) (c := dist v w)
    (fun s' => by linarith [(abs_le.1 (hvw s')).1]) s a b
  simp only [stageMatrix]
  rw [abs_le]
  constructor <;> nlinarith

/-- **The Shapley operator is a `β`-contraction** for `0 ≤ β < 1`. -/
theorem shapleyOp_contracting {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContractingWith (Real.toNNReal β) (G.shapleyOp β) :=
  ⟨Real.toNNReal_lt_one.2 hβ1, LipschitzWith.of_dist_le_mul fun v w => by
    rw [Real.coe_toNNReal _ hβ0]; exact G.dist_shapleyOp_le hβ0 v w⟩

end Shapley

/-! ### Finite-horizon guarantees of stationary strategies -/

/-- If the stationary strategy `x` guarantees `v s` in every one-shot game
`stageMatrix β v s`, then against every behaviour strategy `τ` the `k`-stage discounted sum is
at least `v s - β ^ k * C`, where `|v| ≤ C`. -/
theorem stationary_stageSum_ge {β : ℝ} (hβ : 0 ≤ β) (v : S → ℝ) {C : ℝ} (hC : ∀ s, |v s| ≤ C)
    (x : S → m → ℝ) (hx : ∀ s, x s ∈ mixedStrategies m)
    (hopt : ∀ s, ∀ q ∈ mixedStrategies n, v s ≤ gamePayoff (G.stageMatrix β v s) (x s) q)
    (τ : Strategy (History S m n) S n) :
    ∀ k h s, v s - β ^ k * C ≤ G.stageSum β (Strategy.stationary x hx) τ k h s := by
  intro k
  induction k with
  | zero =>
    intro h s
    simp [stageSum]
    linarith [(abs_le.1 (hC s)).2]
  | succ k ih =>
    intro h s
    simp only [stageSum]
    have hle : ∀ a b, G.stageMatrix β v s a b ≤ G.payoff s a b +
        β * ∑ s', G.trans s a b s' * G.stageSum β (Strategy.stationary x hx) τ k
          (h ++ [(s, a, b)]) s' + β ^ (k + 1) * C := by
      intro a b
      have := G.sum_trans_le (u := v) (w := (fun s' => G.stageSum β (Strategy.stationary x hx) τ k (h ++ [(s, a, b)]) s')) (c := β ^ k * C)
        (fun s' => by linarith [ih (h ++ [(s, a, b)]) s']) s a b
      simp only [stageMatrix, pow_succ]
      nlinarith
    have h1 := gamePayoff_le_add_of_le hle (hx s) (τ.mem h s)
    have h2 := hopt s _ (τ.mem h s)
    simp only [Strategy.stationary] at h1 ⊢
    linarith

/-- The mirror image of `stationary_stageSum_ge` for player 2. -/
theorem stationary_stageSum_le {β : ℝ} (hβ : 0 ≤ β) (v : S → ℝ) {C : ℝ} (hC : ∀ s, |v s| ≤ C)
    (y : S → n → ℝ) (hy : ∀ s, y s ∈ mixedStrategies n)
    (hopt : ∀ s, ∀ p ∈ mixedStrategies m, gamePayoff (G.stageMatrix β v s) p (y s) ≤ v s)
    (σ : Strategy (History S m n) S m) :
    ∀ k h s, G.stageSum β σ (Strategy.stationary y hy) k h s ≤ v s + β ^ k * C := by
  intro k
  induction k with
  | zero =>
    intro h s
    simp [stageSum]
    linarith [(abs_le.1 (hC s)).1]
  | succ k ih =>
    intro h s
    simp only [stageSum]
    have hle : ∀ a b, G.payoff s a b +
        β * ∑ s', G.trans s a b s' * G.stageSum β σ (Strategy.stationary y hy) k
          (h ++ [(s, a, b)]) s' ≤ G.stageMatrix β v s a b + β ^ (k + 1) * C := by
      intro a b
      have := G.sum_trans_le (u := (fun s' => G.stageSum β σ (Strategy.stationary y hy) k (h ++ [(s, a, b)]) s')) (w := v) (c := β ^ k * C)
        (fun s' => by linarith [ih (h ++ [(s, a, b)]) s']) s a b
      simp only [stageMatrix, pow_succ]
      nlinarith
    have h1 := gamePayoff_le_add_of_le hle (σ.mem h s) (hy s)
    have h2 := hopt s _ (σ.mem h s)
    simp only [Strategy.stationary] at h1 ⊢
    linarith

/-! ### Convergence of the discounted sums -/

/-- Successive discounted sums differ by at most `β ^ k * R`, where `|payoff| ≤ R`. -/
theorem abs_stageSum_succ_sub_le {β : ℝ} (hβ : 0 ≤ β) {R : ℝ}
    (hR : ∀ s a b, |G.payoff s a b| ≤ R) (σ : Strategy (History S m n) S m)
    (τ : Strategy (History S m n) S n) :
    ∀ k h s, |G.stageSum β σ τ (k + 1) h s - G.stageSum β σ τ k h s| ≤ β ^ k * R := by
  intro k
  induction k with
  | zero =>
    intro h s
    simp only [stageSum, mul_zero, Finset.sum_const_zero, add_zero, sub_zero, pow_zero, one_mul]
    rw [abs_le]
    exact ⟨le_gamePayoff_of_le (fun a b => (abs_le.1 (hR s a b)).1) (σ.mem h s) (τ.mem h s),
      gamePayoff_le_of_le (fun a b => (abs_le.1 (hR s a b)).2) (σ.mem h s) (τ.mem h s)⟩
  | succ k ih =>
    intro h s
    rw [stageSum, stageSum]
    have hab : ∀ a b, ∀ s', |G.stageSum β σ τ (k + 1) (h ++ [(s, a, b)]) s' -
        G.stageSum β σ τ k (h ++ [(s, a, b)]) s'| ≤ β ^ k * R := fun a b s' => ih _ _
    set M₁ : Matrix m n ℝ := fun a b => G.payoff s a b +
      β * ∑ s', G.trans s a b s' * G.stageSum β σ τ (k + 1) (h ++ [(s, a, b)]) s' with hM₁
    set M₀ : Matrix m n ℝ := fun a b => G.payoff s a b +
      β * ∑ s', G.trans s a b s' * G.stageSum β σ τ k (h ++ [(s, a, b)]) s' with hM₀
    have hβk : 0 ≤ β ^ k := pow_nonneg hβ k
    rw [abs_le]
    constructor
    · have := gamePayoff_le_add_of_le (A := M₀) (B := M₁) (c := β ^ (k + 1) * R) (fun a b => by
        have := G.sum_trans_le (u := (fun s' => G.stageSum β σ τ k (h ++ [(s, a, b)]) s'))
          (w := (fun s' => G.stageSum β σ τ (k + 1) (h ++ [(s, a, b)]) s')) (c := β ^ k * R)
          (fun s' => by linarith [(abs_le.1 (hab a b s')).1]) s a b
        simp only [hM₀, hM₁, pow_succ]; nlinarith) (σ.mem h s) (τ.mem h s)
      linarith
    · have := gamePayoff_le_add_of_le (A := M₁) (B := M₀) (c := β ^ (k + 1) * R) (fun a b => by
        have := G.sum_trans_le (u := (fun s' => G.stageSum β σ τ (k + 1) (h ++ [(s, a, b)]) s'))
          (w := (fun s' => G.stageSum β σ τ k (h ++ [(s, a, b)]) s')) (c := β ^ k * R)
          (fun s' => by linarith [(abs_le.1 (hab a b s')).2]) s a b
        simp only [hM₀, hM₁, pow_succ]; nlinarith) (σ.mem h s) (τ.mem h s)
      linarith

lemma exists_payoff_bound : ∃ R, ∀ s a b, |G.payoff s a b| ≤ R := by
  obtain ⟨R, hR⟩ := (Set.finite_range fun x : S × m × n => |G.payoff x.1 x.2.1 x.2.2|).bddAbove
  exact ⟨R, fun s a b => hR ⟨(s, a, b), rfl⟩⟩

/-- The expected discounted payoff of the infinite game started in state `s` (the limit of the
`k`-stage discounted sums; it exists when `0 ≤ β < 1`, see `tendsto_stageSum`). -/
noncomputable def discountedPayoff (β : ℝ) (σ : Strategy (History S m n) S m)
    (τ : Strategy (History S m n) S n) (s : S) : ℝ :=
  limUnder atTop fun k => G.stageSum β σ τ k [] s

/-- For `0 ≤ β < 1`, the `k`-stage discounted sums converge to `discountedPayoff`. -/
theorem tendsto_stageSum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (σ : Strategy (History S m n) S m) (τ : Strategy (History S m n) S n) (s : S) :
    Tendsto (fun k => G.stageSum β σ τ k [] s) atTop (𝓝 (G.discountedPayoff β σ τ s)) := by
  obtain ⟨R, hR⟩ := G.exists_payoff_bound
  refine CauchySeq.tendsto_limUnder (cauchySeq_of_le_geometric β R hβ1 fun k => ?_)
  rw [Real.dist_eq, abs_sub_comm, mul_comm]
  exact G.abs_stageSum_succ_sub_le hβ0 hR σ τ k [] s

/-- **Stationary guarantee, player 1.** If `x` guarantees `v s` in every one-shot game
`stageMatrix β v s`, then `x` guarantees discounted payoff at least `v s` from every state
against every behaviour strategy. -/
theorem stationary_guarantee_ge {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (v : S → ℝ)
    (x : S → m → ℝ) (hx : ∀ s, x s ∈ mixedStrategies m)
    (hopt : ∀ s, ∀ q ∈ mixedStrategies n, v s ≤ gamePayoff (G.stageMatrix β v s) (x s) q)
    (τ : Strategy (History S m n) S n) (s : S) :
    v s ≤ G.discountedPayoff β (Strategy.stationary x hx) τ s := by
  have hC : ∀ s, |v s| ≤ ‖v‖ := fun s => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v s
  have hlim : Tendsto (fun k : ℕ => v s - β ^ k * ‖v‖) atTop (𝓝 (v s)) := by
    simpa using tendsto_const_nhds.sub
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const ‖v‖)
  exact le_of_tendsto_of_tendsto' hlim (G.tendsto_stageSum hβ0 hβ1 _ τ s)
    fun k => G.stationary_stageSum_ge hβ0 v hC x hx hopt τ k [] s

/-- **Stationary guarantee, player 2.** -/
theorem stationary_guarantee_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (v : S → ℝ)
    (y : S → n → ℝ) (hy : ∀ s, y s ∈ mixedStrategies n)
    (hopt : ∀ s, ∀ p ∈ mixedStrategies m, gamePayoff (G.stageMatrix β v s) p (y s) ≤ v s)
    (σ : Strategy (History S m n) S m) (s : S) :
    G.discountedPayoff β σ (Strategy.stationary y hy) s ≤ v s := by
  have hC : ∀ s, |v s| ≤ ‖v‖ := fun s => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v s
  have hlim : Tendsto (fun k : ℕ => v s + β ^ k * ‖v‖) atTop (𝓝 (v s)) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const ‖v‖)
  exact le_of_tendsto_of_tendsto' (G.tendsto_stageSum hβ0 hβ1 σ _ s) hlim
    fun k => G.stationary_stageSum_le hβ0 v hC y hy hopt σ k [] s

/-! ### Shapley's theorem -/

section ShapleyTheorem

variable [Nonempty m] [Nonempty n]

/-- **Shapley's theorem (1953).** For `0 ≤ β < 1`, the discounted two-player zero-sum
stochastic game has a value vector `v`: `v` is the unique solution of the Shapley equation
`v s = val (stageMatrix β v s)`, and there are stationary strategies `x` of player 1 and `y` of
player 2 such that `x` guarantees discounted payoff at least `v s` against every behaviour
strategy of player 2, and `y` holds every behaviour strategy of player 1 to at most `v s`, from
every initial state `s`. -/
theorem shapley_theorem {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ v : S → ℝ, (∀ s, v s = matrixValue (G.stageMatrix β v s)) ∧
      (∀ w : S → ℝ, (∀ s, w s = matrixValue (G.stageMatrix β w s)) → w = v) ∧
      ∃ (x : S → m → ℝ) (hx : ∀ s, x s ∈ mixedStrategies m)
        (y : S → n → ℝ) (hy : ∀ s, y s ∈ mixedStrategies n),
        (∀ s (τ : Strategy (History S m n) S n),
          v s ≤ G.discountedPayoff β (Strategy.stationary x hx) τ s) ∧
        (∀ s (σ : Strategy (History S m n) S m),
          G.discountedPayoff β σ (Strategy.stationary y hy) s ≤ v s) := by
  have hT := G.shapleyOp_contracting hβ0 hβ1
  set v := ContractingWith.fixedPoint (G.shapleyOp β) hT
  have hv : ∀ s, v s = matrixValue (G.stageMatrix β v s) := fun s =>
    (congrFun (ContractingWith.fixedPoint_isFixedPt (f := G.shapleyOp β) hT) s).symm
  refine ⟨v, hv, fun w hw => ContractingWith.fixedPoint_unique hT (funext fun s => (hw s).symm),
    ?_⟩
  choose x hx hxopt using fun s => (matrixValue_spec (G.stageMatrix β v s)).1
  choose y hy hyopt using fun s => (matrixValue_spec (G.stageMatrix β v s)).2
  refine ⟨x, hx, y, hy, fun s τ => ?_, fun s σ => ?_⟩
  · exact G.stationary_guarantee_ge hβ0 hβ1 v x hx (fun s q hq => (hv s).trans_le (hxopt s q hq))
      τ s
  · exact G.stationary_guarantee_le hβ0 hβ1 v y hy (fun s p hp => (hyopt s p hp).trans (hv s).ge)
      σ s

omit [Nonempty m] [Nonempty n] in
/-- If, for some vector `v`, the stationary strategy `x` guarantees at least `v s` and the
stationary strategy `y` concedes at most `v s` in every one-shot game `stageMatrix β v s`
(this forces `v` to be the fixed point of the Shapley operator), then the discounted payoff of
`(x, y)` is exactly `v s`; by `stationary_guarantee_ge` / `stationary_guarantee_le` both are
optimal. -/
theorem discountedPayoff_eq_of_optimal {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (v : S → ℝ)
    (x : S → m → ℝ) (hx : ∀ s, x s ∈ mixedStrategies m)
    (hxopt : ∀ s, ∀ q ∈ mixedStrategies n, v s ≤ gamePayoff (G.stageMatrix β v s) (x s) q)
    (y : S → n → ℝ) (hy : ∀ s, y s ∈ mixedStrategies n)
    (hyopt : ∀ s, ∀ p ∈ mixedStrategies m, gamePayoff (G.stageMatrix β v s) p (y s) ≤ v s)
    (s : S) :
    G.discountedPayoff β (Strategy.stationary x hx) (Strategy.stationary y hy) s = v s :=
  le_antisymm (G.stationary_guarantee_le hβ0 hβ1 v y hy hyopt _ s)
    (G.stationary_guarantee_ge hβ0 hβ1 v x hx hxopt _ s)

end ShapleyTheorem

/-! ### Undiscounted games: uniform value from the average-payoff optimality equation -/

/-- If `(g, w)` satisfies the average-payoff optimality inequality for player 1 with the
stationary strategy `x` (`g + w s ≤ x s ⬝ [payoff + ∑ trans * w] ⬝ q` for every mixed `q`), then
against every behaviour strategy the undiscounted `k`-stage total is at least
`k * g + w s - C`, where `|w| ≤ C`. -/
theorem acoe_stageSum_ge (g : ℝ) (w : S → ℝ) {C : ℝ} (hC : ∀ s, |w s| ≤ C)
    (x : S → m → ℝ) (hx : ∀ s, x s ∈ mixedStrategies m)
    (hopt : ∀ s, ∀ q ∈ mixedStrategies n, g + w s ≤ gamePayoff (G.stageMatrix 1 w s) (x s) q)
    (τ : Strategy (History S m n) S n) :
    ∀ (k : ℕ) h s, k * g + w s - C ≤ G.stageSum 1 (Strategy.stationary x hx) τ k h s := by
  intro k
  induction k with
  | zero =>
    intro h s
    simp [stageSum]
    linarith [(abs_le.1 (hC s)).2]
  | succ k ih =>
    intro h s
    simp only [stageSum]
    have hle : ∀ a b, G.stageMatrix 1 w s a b ≤ G.payoff s a b +
        1 * ∑ s', G.trans s a b s' * G.stageSum 1 (Strategy.stationary x hx) τ k
          (h ++ [(s, a, b)]) s' + (C - k * g) := by
      intro a b
      have := G.sum_trans_le (u := w)
        (w := fun s' => G.stageSum 1 (Strategy.stationary x hx) τ k (h ++ [(s, a, b)]) s')
        (c := C - k * g) (fun s' => by linarith [ih (h ++ [(s, a, b)]) s']) s a b
      simp only [stageMatrix]
      linarith
    have h1 := gamePayoff_le_add_of_le hle (hx s) (τ.mem h s)
    have h2 := hopt s _ (τ.mem h s)
    simp only [Strategy.stationary] at h1 ⊢
    push_cast
    linarith

/-- The mirror image of `acoe_stageSum_ge` for player 2. -/
theorem acoe_stageSum_le (g : ℝ) (w : S → ℝ) {C : ℝ} (hC : ∀ s, |w s| ≤ C)
    (y : S → n → ℝ) (hy : ∀ s, y s ∈ mixedStrategies n)
    (hopt : ∀ s, ∀ p ∈ mixedStrategies m, gamePayoff (G.stageMatrix 1 w s) p (y s) ≤ g + w s)
    (σ : Strategy (History S m n) S m) :
    ∀ (k : ℕ) h s, G.stageSum 1 σ (Strategy.stationary y hy) k h s ≤ k * g + w s + C := by
  intro k
  induction k with
  | zero =>
    intro h s
    simp [stageSum]
    linarith [(abs_le.1 (hC s)).1]
  | succ k ih =>
    intro h s
    simp only [stageSum]
    have hle : ∀ a b, G.payoff s a b +
        1 * ∑ s', G.trans s a b s' * G.stageSum 1 σ (Strategy.stationary y hy) k
          (h ++ [(s, a, b)]) s' ≤ G.stageMatrix 1 w s a b + (C + k * g) := by
      intro a b
      have := G.sum_trans_le
        (u := fun s' => G.stageSum 1 σ (Strategy.stationary y hy) k (h ++ [(s, a, b)]) s')
        (w := w) (c := C + k * g) (fun s' => by linarith [ih (h ++ [(s, a, b)]) s']) s a b
      simp only [stageMatrix]
      linarith
    have h1 := gamePayoff_le_add_of_le hle (σ.mem h s) (hy s)
    have h2 := hopt s _ (σ.mem h s)
    simp only [Strategy.stationary] at h1 ⊢
    push_cast
    linarith

/-- **Uniform value from the average-payoff optimality equation.** Suppose `g : ℝ`,
`w : S → ℝ` and stationary strategies `x`, `y` satisfy, in every state `s`,
`x s ⬝ [payoff + ∑ trans * w] ⬝ q ≥ g + w s` for all mixed `q` and
`p ⬝ [payoff + ∑ trans * w] ⬝ y s ≤ g + w s` for all mixed `p`. Then for every `ε > 0` there is
`N` such that for all `k ≥ N` and every initial state, `x` guarantees a `k`-stage average payoff
at least `g - ε` against every behaviour strategy, and `y` holds every behaviour strategy to at
most `g + ε`: `g` is the uniform value and `x`, `y` are uniformly `ε`-optimal. -/
theorem uniform_value_of_acoe (g : ℝ) (w : S → ℝ)
    (x : S → m → ℝ) (hx : ∀ s, x s ∈ mixedStrategies m)
    (hxopt : ∀ s, ∀ q ∈ mixedStrategies n, g + w s ≤ gamePayoff (G.stageMatrix 1 w s) (x s) q)
    (y : S → n → ℝ) (hy : ∀ s, y s ∈ mixedStrategies n)
    (hyopt : ∀ s, ∀ p ∈ mixedStrategies m, gamePayoff (G.stageMatrix 1 w s) p (y s) ≤ g + w s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∀ s,
      (∀ τ : Strategy (History S m n) S n,
        g - ε ≤ G.stageSum 1 (Strategy.stationary x hx) τ k [] s / k) ∧
      (∀ σ : Strategy (History S m n) S m,
        G.stageSum 1 σ (Strategy.stationary y hy) k [] s / k ≤ g + ε) := by
  have hC : ∀ s, |w s| ≤ ‖w‖ := fun s => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w s
  have hC0 : 0 ≤ ‖w‖ := norm_nonneg w
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖w‖ / ε)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (by linarith) hε.le) hN
  have hNε : 2 * ‖w‖ < N * ε := by rwa [div_lt_iff₀ hε] at hN
  refine ⟨N, fun k hk s => ⟨fun τ => ?_, fun σ => ?_⟩⟩
  · have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := lt_of_lt_of_le hNpos hk'
    rw [le_div_iff₀ hkpos]
    have := G.acoe_stageSum_ge g w hC x hx hxopt τ k [] s
    have hws := (abs_le.1 (hC s)).1
    nlinarith
  · have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := lt_of_lt_of_le hNpos hk'
    rw [div_le_iff₀ hkpos]
    have := G.acoe_stageSum_le g w hC y hy hyopt σ k [] s
    have hws := (abs_le.1 (hC s)).2
    nlinarith

section ConstValue

variable [Nonempty m] [Nonempty n]

/-- **Uniform value when all stage games have the same value.** If the one-shot matrix game
`payoff s` has the same value `g` in every state, then (whatever the transitions) `g` is the
uniform value of the undiscounted game, and stationary strategies that are optimal in every
one-shot game are uniformly `ε`-optimal for every `ε > 0`. -/
theorem uniform_value_of_const_value (g : ℝ) (hg : ∀ s, matrixValue (G.payoff s) = g) :
    ∃ (x : S → m → ℝ) (hx : ∀ s, x s ∈ mixedStrategies m)
      (y : S → n → ℝ) (hy : ∀ s, y s ∈ mixedStrategies n),
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k, N ≤ k → ∀ s,
        (∀ τ : Strategy (History S m n) S n,
          g - ε ≤ G.stageSum 1 (Strategy.stationary x hx) τ k [] s / k) ∧
        (∀ σ : Strategy (History S m n) S m,
          G.stageSum 1 σ (Strategy.stationary y hy) k [] s / k ≤ g + ε) := by
  have hst : ∀ s, G.stageMatrix 1 0 s = G.payoff s := fun s => by
    funext a b; simp [stageMatrix]
  choose x hx hxopt using fun s => (matrixValue_spec (G.payoff s)).1
  choose y hy hyopt using fun s => (matrixValue_spec (G.payoff s)).2
  refine ⟨x, hx, y, hy, fun ε hε => G.uniform_value_of_acoe g 0 x hx ?_ y hy ?_ hε⟩
  · intro s q hq
    rw [hst, Pi.zero_apply, add_zero, ← hg s]
    exact hxopt s q hq
  · intro s p hp
    rw [hst, Pi.zero_apply, add_zero, ← hg s]
    exact hyopt s p hp

/-- **Repeated matrix games.** With a single state, the uniform value of the undiscounted game
is the value of the stage matrix game, attained (up to `ε`) by repeating a one-shot optimal
strategy. -/
theorem uniform_value_repeated_game [Unique S] :
    ∃ (x : S → m → ℝ) (hx : ∀ s, x s ∈ mixedStrategies m)
      (y : S → n → ℝ) (hy : ∀ s, y s ∈ mixedStrategies n),
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k, N ≤ k → ∀ s,
        (∀ τ : Strategy (History S m n) S n,
          matrixValue (G.payoff default) - ε ≤
            G.stageSum 1 (Strategy.stationary x hx) τ k [] s / k) ∧
        (∀ σ : Strategy (History S m n) S m,
          G.stageSum 1 σ (Strategy.stationary y hy) k [] s / k ≤
            matrixValue (G.payoff default) + ε) :=
  G.uniform_value_of_const_value _ fun s => by rw [Subsingleton.elim s default]

end ConstValue

end ZeroSumStochasticGame

end Applied.Economics
