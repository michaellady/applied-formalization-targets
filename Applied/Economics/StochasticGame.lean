import Mathlib.Tactic

/-!
# Finite stochastic games and uniform ε-equilibria: definitions

* `StochasticGame I S A`: finitely many players `I`, states `S`, and actions `A i` for
  player `i`. In state `s`, the players simultaneously choose an action profile
  `a : ∀ i, A i`; player `i` receives the stage payoff `payoff s a i` and the next state is
  `s'` with probability `trans s a s'`.
* A *history* is the list of the (state, action profile) pairs of the stages played so far, in
  chronological order; play is perfectly monitored.
* `BehaviourStrategy S A i`: for every history and every current state, a probability
  distribution on `A i`. `Profile S A`: one behaviour strategy per player. Players randomise
  independently.
* `nStageSum G σ n h s i`: the expected sum of player `i`'s payoffs over the next `n` stages,
  when the history is `h`, the current state is `s` and the players follow `σ`. It is defined
  by recursion on `n` (a finite sum over action profiles and next states), so no measure
  theory is needed.
* `avgPayoff G σ n s i = nStageSum G σ n [] s i / n`: the expected average payoff of player
  `i` in the `n`-stage game starting in state `s`.
* `IsUniformEquilibrium G ε σ`: there is `N` such that for every `n ≥ N`, every initial state,
  every player `i` and every behaviour strategy `τ` of player `i`, deviating to `τ` gains at
  most `ε` in the `n`-stage game: `σ` is an `ε`-equilibrium of every sufficiently long finitely
  repeated game, with `N` independent of the deviation.

Sanity checks: `avgPayoff_of_const` (if the stage payoff of player `i` is a constant `c`, his
expected `n`-stage average payoff is `c` for every `n ≥ 1` and every profile) and
`isUniformEquilibrium_of_const` (if all stage payoffs are constant, every profile is a uniform
`ε`-equilibrium for every `ε ≥ 0`).
-/

open Finset

open Classical

noncomputable section

namespace Applied.Economics

/-- A finite stochastic game: transition probabilities and stage payoffs. -/
structure StochasticGame (I S : Type*) (A : I → Type*) [Fintype S] where
  /-- `trans s a s'`: probability that the next state is `s'` when `a` is played in `s`. -/
  trans : S → (∀ i, A i) → S → ℝ
  trans_nonneg : ∀ s a s', 0 ≤ trans s a s'
  trans_sum : ∀ s a, ∑ s', trans s a s' = 1
  /-- `payoff s a i`: stage payoff of player `i` when `a` is played in `s`. -/
  payoff : S → (∀ i, A i) → I → ℝ

namespace StochasticGame

variable {I S : Type*} {A : I → Type*} [Fintype I] [Fintype S] [∀ i, Fintype (A i)]

/-- A history: the states visited and action profiles played in the past stages, in
chronological order. -/
abbrev History (S : Type*) (A : I → Type*) := List (S × (∀ i, A i))

/-- A behaviour strategy of player `i`: a mixed action for every history and current state. -/
structure BehaviourStrategy (S : Type*) (A : I → Type*) [∀ i, Fintype (A i)] (i : I) where
  /-- `prob h s x`: probability of playing `x` after history `h` in the current state `s`. -/
  prob : History S A → S → A i → ℝ
  prob_nonneg : ∀ h s x, 0 ≤ prob h s x
  prob_sum : ∀ h s, ∑ x, prob h s x = 1

/-- A profile of behaviour strategies. -/
abbrev Profile (S : Type*) (A : I → Type*) [∀ i, Fintype (A i)] :=
  ∀ i, BehaviourStrategy S A i

/-- Expected sum of player `i`'s stage payoffs over the next `n` stages, after history `h`, in
the current state `s`, under the profile `σ`. -/
def nStageSum (G : StochasticGame I S A) (σ : Profile S A) :
    ℕ → History S A → S → I → ℝ
  | 0, _, _, _ => 0
  | n + 1, h, s, i => ∑ a : (∀ j, A j), (∏ j, (σ j).prob h s (a j)) *
      (G.payoff s a i + ∑ s', G.trans s a s' * nStageSum G σ n (h ++ [(s, a)]) s' i)

/-- Expected average payoff of player `i` in the `n`-stage game with initial state `s`. -/
def avgPayoff (G : StochasticGame I S A) (σ : Profile S A) (n : ℕ) (s : S) (i : I) : ℝ :=
  nStageSum G σ n [] s i / n

/-- `σ` is a uniform `ε`-equilibrium: an `ε`-equilibrium of every `n`-stage game with `n`
large enough, for every initial state. -/
def IsUniformEquilibrium (G : StochasticGame I S A) (ε : ℝ) (σ : Profile S A) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → ∀ (s : S) (i : I) (τ : BehaviourStrategy S A i),
    avgPayoff G (Function.update σ i τ) n s i ≤ avgPayoff G σ n s i + ε

omit [Fintype S] in
/-- The probabilities of the action profiles sum to one. -/
lemma sum_prod_prob (σ : Profile S A) (h : History S A) (s : S) :
    ∑ a : (∀ j, A j), ∏ j, (σ j).prob h s (a j) = 1 := by
  have := Finset.prod_univ_sum (fun (j : I) => (univ : Finset (A j)))
    (fun j x => (σ j).prob h s x)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp [BehaviourStrategy.prob_sum]

/-- If player `i`'s stage payoff is the constant `c`, then the expected `n`-stage total payoff of
player `i` is `n * c`, for every strategy profile, history and state. -/
lemma nStageSum_of_const (G : StochasticGame I S A) (σ : Profile S A) (i : I) (c : ℝ)
    (hc : ∀ s a, G.payoff s a i = c) (n : ℕ) (h : History S A) (s : S) :
    nStageSum G σ n h s i = n * c := by
  induction n generalizing h s with
  | zero => simp [nStageSum]
  | succ n ih =>
    simp only [nStageSum, hc, ih, ← Finset.sum_mul, G.trans_sum, sum_prod_prob]
    push_cast
    ring

/-- If player `i`'s stage payoff is the constant `c`, his `n`-stage average payoff is `c`. -/
theorem avgPayoff_of_const (G : StochasticGame I S A) (σ : Profile S A) (i : I) (c : ℝ)
    (hc : ∀ s a, G.payoff s a i = c) {n : ℕ} (hn : 0 < n) (s : S) :
    avgPayoff G σ n s i = c := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [avgPayoff, nStageSum_of_const G σ i c hc]
  field_simp

/-- If every stage payoff is constant, every profile is a uniform `ε`-equilibrium (`ε ≥ 0`). -/
theorem isUniformEquilibrium_of_const (G : StochasticGame I S A) (c : I → ℝ)
    (hc : ∀ s a i, G.payoff s a i = c i) {ε : ℝ} (hε : 0 ≤ ε) (σ : Profile S A) :
    IsUniformEquilibrium G ε σ := by
  refine ⟨1, fun n hn s i τ => ?_⟩
  rw [avgPayoff_of_const G _ i (c i) (fun s a => hc s a i) hn,
    avgPayoff_of_const G _ i (c i) (fun s a => hc s a i) hn]
  linarith

end StochasticGame

end Applied.Economics
