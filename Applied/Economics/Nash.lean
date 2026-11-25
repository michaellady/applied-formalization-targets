import Applied.Economics.Minimax

/-!
# Nash equilibria: zero-sum games and potential games

Mathlib (at the pinned revision) has no Brouwer or Kakutani fixed-point theorem, so Nash's
existence theorem for general finite games is not proved here. This file proves the two
classical special cases that do not need a fixed-point theorem, and sets up the definitions for
the general statement.

## Two-player games

For payoff matrices `A`, `B : Matrix m n ℝ` (row player receives `pᵀ A q`, column player
`pᵀ B q`), `IsBimatrixNash A B p q` says that `p`, `q` are mixed strategies and neither player
gains by a unilateral deviation to another mixed strategy.

* `exists_isBimatrixNash_zeroSum`: a zero-sum game (`B = -A`) has a Nash equilibrium.
* `isBimatrixNash_zeroSum_iff_optimal`: the Nash equilibria of a zero-sum game are exactly the
  pairs of a maximin strategy of the row player and a minimax strategy of the column player.
* `isBimatrixNash_zeroSum_interchange`, `gamePayoff_eq_of_isBimatrixNash_zeroSum`: equilibria
  of a zero-sum game are interchangeable and all give the same payoff.

## Games with any number of players

A game in strategic form has players `i : ι`, pure strategies `S i` and payoffs
`u i : (∀ j, S j) → ℝ`.

* `IsPureNash u s`, `IsMixedNash u σ` (with expected payoff `mixedPayoff u σ i`).
* `exists_isPureNash_of_potential`: a finite game with a generalized ordinal potential (in
  particular an exact potential) has a pure Nash equilibrium, namely any maximiser of the
  potential.
* `isMixedNash_pure_iff`: a pure profile, viewed as a mixed profile, is a mixed Nash
  equilibrium iff it is a pure Nash equilibrium. Hence `exists_isMixedNash_of_potential`.
-/

open Matrix Set

namespace Applied.Economics

/-! ### Two-player games -/

section Bimatrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A mixed Nash equilibrium of the two-player game in which the row player receives
`gamePayoff A p q = pᵀ A q` and the column player receives `gamePayoff B p q = pᵀ B q`. -/
def IsBimatrixNash (A B : Matrix m n ℝ) (p : m → ℝ) (q : n → ℝ) : Prop :=
  p ∈ mixedStrategies m ∧ q ∈ mixedStrategies n ∧
    (∀ p' ∈ mixedStrategies m, gamePayoff A p' q ≤ gamePayoff A p q) ∧
    (∀ q' ∈ mixedStrategies n, gamePayoff B p q' ≤ gamePayoff B p q)

lemma gamePayoff_neg (A : Matrix m n ℝ) (p : m → ℝ) (q : n → ℝ) :
    gamePayoff (-A) p q = -gamePayoff A p q := by
  simp [gamePayoff, neg_mulVec]

/-- In a zero-sum game a Nash equilibrium is the same thing as a saddle point of the row
player's payoff. -/
lemma isBimatrixNash_zeroSum_iff (A : Matrix m n ℝ) (p : m → ℝ) (q : n → ℝ) :
    IsBimatrixNash A (-A) p q ↔ p ∈ mixedStrategies m ∧ q ∈ mixedStrategies n ∧
      (∀ p' ∈ mixedStrategies m, gamePayoff A p' q ≤ gamePayoff A p q) ∧
      (∀ q' ∈ mixedStrategies n, gamePayoff A p q ≤ gamePayoff A p q') := by
  simp only [IsBimatrixNash, gamePayoff_neg, neg_le_neg_iff]

/-- **Existence of Nash equilibrium in finite two-player zero-sum games.** -/
theorem exists_isBimatrixNash_zeroSum [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) :
    ∃ p q, IsBimatrixNash A (-A) p q := by
  obtain ⟨p, hp, q, hq, h1, h2⟩ := exists_saddle_point A
  exact ⟨p, q, (isBimatrixNash_zeroSum_iff A p q).mpr ⟨hp, hq, h1, h2⟩⟩

/-- `p` is a maximin (optimal) strategy of the row player: it is a mixed strategy, and any
payoff level `v` that some mixed strategy `p'` guarantees against all mixed strategies of the
column player is also guaranteed by `p`. -/
def IsMaximinStrategy (A : Matrix m n ℝ) (p : m → ℝ) : Prop :=
  p ∈ mixedStrategies m ∧ ∀ p' ∈ mixedStrategies m, ∀ v : ℝ,
    (∀ q ∈ mixedStrategies n, v ≤ gamePayoff A p' q) → ∀ q ∈ mixedStrategies n, v ≤ gamePayoff A p q

/-- `q` is a minimax (optimal) strategy of the column player: it is a mixed strategy, and any
level `v` to which some mixed strategy `q'` holds the row player is also enforced by `q`. -/
def IsMinimaxStrategy (A : Matrix m n ℝ) (q : n → ℝ) : Prop :=
  q ∈ mixedStrategies n ∧ ∀ q' ∈ mixedStrategies n, ∀ v : ℝ,
    (∀ p ∈ mixedStrategies m, gamePayoff A p q' ≤ v) → ∀ p ∈ mixedStrategies m, gamePayoff A p q ≤ v

/-- **Nash equilibria of a zero-sum game are exactly the pairs of optimal strategies.** -/
theorem isBimatrixNash_zeroSum_iff_optimal [Nonempty m] [Nonempty n] (A : Matrix m n ℝ)
    (p : m → ℝ) (q : n → ℝ) :
    IsBimatrixNash A (-A) p q ↔ IsMaximinStrategy A p ∧ IsMinimaxStrategy A q := by
  rw [isBimatrixNash_zeroSum_iff]
  constructor
  · rintro ⟨hp, hq, h1, h2⟩
    refine ⟨⟨hp, fun p' hp' v hv q' hq' => ?_⟩, ⟨hq, fun q' hq' v hv p' hp' => ?_⟩⟩
    · exact (hv q hq).trans ((h1 p' hp').trans (h2 q' hq'))
    · exact (h1 p' hp').trans ((h2 q' hq').trans (hv p hp))
  · rintro ⟨⟨hp, hpopt⟩, ⟨hq, hqopt⟩⟩
    obtain ⟨p₀, hp₀, q₀, hq₀, h1, h2⟩ := exists_saddle_point A
    have hrow := hpopt p₀ hp₀ (gamePayoff A p₀ q₀) h2
    have hcol := hqopt q₀ hq₀ (gamePayoff A p₀ q₀) h1
    have e : gamePayoff A p q = gamePayoff A p₀ q₀ := le_antisymm (hcol p hp) (hrow q hq)
    refine ⟨hp, hq, fun p' hp' => ?_, fun q' hq' => ?_⟩
    · rw [e]; exact hcol p' hp'
    · rw [e]; exact hrow q' hq'

/-- Equivalent description: `(p, q)` is a Nash equilibrium of the zero-sum game iff, for some
number `v`, `p` guarantees the row player at least `v` and `q` holds the row player to at
most `v`. (By `value_unique`, such a `v` is the value of the game.) -/
theorem isBimatrixNash_zeroSum_iff_exists_value (A : Matrix m n ℝ) (p : m → ℝ) (q : n → ℝ) :
    IsBimatrixNash A (-A) p q ↔ p ∈ mixedStrategies m ∧ q ∈ mixedStrategies n ∧
      ∃ v : ℝ, (∀ q' ∈ mixedStrategies n, v ≤ gamePayoff A p q') ∧
        (∀ p' ∈ mixedStrategies m, gamePayoff A p' q ≤ v) := by
  rw [isBimatrixNash_zeroSum_iff]
  constructor
  · rintro ⟨hp, hq, h1, h2⟩
    exact ⟨hp, hq, gamePayoff A p q, h2, h1⟩
  · rintro ⟨hp, hq, v, hrow, hcol⟩
    have e : gamePayoff A p q = v := le_antisymm (hcol p hp) (hrow q hq)
    exact ⟨hp, hq, fun p' hp' => e ▸ hcol p' hp', fun q' hq' => e ▸ hrow q' hq'⟩

/-- All Nash equilibria of a zero-sum game give the same payoff. -/
theorem gamePayoff_eq_of_isBimatrixNash_zeroSum (A : Matrix m n ℝ) {p p' : m → ℝ}
    {q q' : n → ℝ} (h : IsBimatrixNash A (-A) p q) (h' : IsBimatrixNash A (-A) p' q') :
    gamePayoff A p q = gamePayoff A p' q' := by
  rw [isBimatrixNash_zeroSum_iff] at h h'
  obtain ⟨hp, hq, h1, h2⟩ := h
  obtain ⟨hp', hq', h1', h2'⟩ := h'
  exact le_antisymm ((h2 q' hq').trans (h1' p hp)) ((h2' q hq).trans (h1 p' hp'))

/-- Interchangeability: if `(p, q)` and `(p', q')` are Nash equilibria of a zero-sum game, so
is `(p, q')`. -/
theorem isBimatrixNash_zeroSum_interchange (A : Matrix m n ℝ) {p p' : m → ℝ}
    {q q' : n → ℝ} (h : IsBimatrixNash A (-A) p q) (h' : IsBimatrixNash A (-A) p' q') :
    IsBimatrixNash A (-A) p q' := by
  have e := gamePayoff_eq_of_isBimatrixNash_zeroSum A h h'
  rw [isBimatrixNash_zeroSum_iff_exists_value]
  rw [isBimatrixNash_zeroSum_iff] at h h'
  obtain ⟨hp, hq, h1, h2⟩ := h
  obtain ⟨hp', hq', h1', h2'⟩ := h'
  exact ⟨hp, hq', gamePayoff A p q, h2, fun p'' hp'' => e ▸ h1' p'' hp''⟩

end Bimatrix

/-! ### Games in strategic form -/

section Strategic

variable {ι : Type*} {S : ι → Type*}

/-- A pure Nash equilibrium: no player gains by unilaterally switching to another pure
strategy. -/
def IsPureNash [DecidableEq ι] (u : ι → (∀ j, S j) → ℝ) (s : ∀ j, S j) : Prop :=
  ∀ i (a : S i), u i (Function.update s i a) ≤ u i s

/-- `Φ` is a generalized ordinal potential: whenever a unilateral deviation strictly raises the
deviator's payoff, it strictly raises `Φ`. -/
def IsGeneralizedOrdinalPotential [DecidableEq ι] (u : ι → (∀ j, S j) → ℝ)
    (Φ : (∀ j, S j) → ℝ) : Prop :=
  ∀ i (s : ∀ j, S j) (a : S i), u i s < u i (Function.update s i a) → Φ s < Φ (Function.update s i a)

/-- `Φ` is an exact potential (Monderer–Shapley): the change in a deviator's payoff equals the
change in `Φ`. -/
def IsExactPotential [DecidableEq ι] (u : ι → (∀ j, S j) → ℝ) (Φ : (∀ j, S j) → ℝ) : Prop :=
  ∀ i (s : ∀ j, S j) (a : S i),
    u i (Function.update s i a) - u i s = Φ (Function.update s i a) - Φ s

lemma IsExactPotential.isGeneralizedOrdinalPotential [DecidableEq ι] {u : ι → (∀ j, S j) → ℝ}
    {Φ : (∀ j, S j) → ℝ} (h : IsExactPotential u Φ) : IsGeneralizedOrdinalPotential u Φ := by
  intro i s a hlt
  have := h i s a
  linarith

/-- A maximiser of a generalized ordinal potential is a pure Nash equilibrium. -/
theorem isPureNash_of_potential_max [DecidableEq ι] {u : ι → (∀ j, S j) → ℝ}
    {Φ : (∀ j, S j) → ℝ} (hΦ : IsGeneralizedOrdinalPotential u Φ) {s : ∀ j, S j}
    (hmax : ∀ s', Φ s' ≤ Φ s) : IsPureNash u s := by
  intro i a
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (hΦ i s a hlt) (not_lt.mpr (hmax _))

/-- **Finite potential games have a pure Nash equilibrium.** -/
theorem exists_isPureNash_of_potential [DecidableEq ι] [Finite ι] [∀ i, Finite (S i)]
    [∀ i, Nonempty (S i)] (u : ι → (∀ j, S j) → ℝ) (Φ : (∀ j, S j) → ℝ)
    (hΦ : IsGeneralizedOrdinalPotential u Φ) : ∃ s, IsPureNash u s := by
  obtain ⟨s, hs⟩ := Finite.exists_max Φ
  exact ⟨s, isPureNash_of_potential_max hΦ hs⟩

/-- Finite games with an exact potential have a pure Nash equilibrium. -/
theorem exists_isPureNash_of_exactPotential [DecidableEq ι] [Finite ι] [∀ i, Finite (S i)]
    [∀ i, Nonempty (S i)] (u : ι → (∀ j, S j) → ℝ) (Φ : (∀ j, S j) → ℝ)
    (hΦ : IsExactPotential u Φ) : ∃ s, IsPureNash u s :=
  exists_isPureNash_of_potential u Φ hΦ.isGeneralizedOrdinalPotential

variable [Fintype ι] [∀ i, Fintype (S i)]

/-- Expected payoff of player `i` when every player `j` independently randomises according to
`σ j`: the sum over pure profiles `s` of the product probability `∏ j, σ j (s j)` times
`u i s`. -/
def mixedPayoff [DecidableEq ι] (u : ι → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ) (i : ι) : ℝ :=
  ∑ s : ∀ j, S j, (∏ j, σ j (s j)) * u i s

/-- A mixed Nash equilibrium: every `σ i` is a probability vector on `S i`, and no player can
raise their expected payoff by unilaterally switching to another mixed strategy. -/
def IsMixedNash [DecidableEq ι] (u : ι → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ) : Prop :=
  (∀ i, σ i ∈ mixedStrategies (S i)) ∧
    ∀ i, ∀ τ ∈ mixedStrategies (S i), mixedPayoff u (Function.update σ i τ) i ≤ mixedPayoff u σ i

/-- The mixed profile in which every player `j` plays the pure strategy `s j` for sure. -/
def pureProfile [∀ i, DecidableEq (S i)] (s : ∀ j, S j) : ∀ j, S j → ℝ :=
  fun j => Pi.single (s j) 1

/-- Expected payoff when everybody plays the pure profile `s` except player `i`, who mixes
with `τ`. -/
lemma mixedPayoff_update_pureProfile [DecidableEq ι] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ j, S j) → ℝ) (s : ∀ j, S j) (i : ι) (τ : S i → ℝ) (k : ι) :
    mixedPayoff u (Function.update (pureProfile s) i τ) k
      = ∑ a, τ a * u k (Function.update s i a) := by
  have hprod : ∀ s' : ∀ j, S j, ∏ j, (Function.update (pureProfile s) i τ) j (s' j)
      = if s' = Function.update s i (s' i) then τ (s' i) else 0 := by
    intro s'
    split_ifs with h
    · rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        have : s' j = s j := by
          have := congrFun h j
          rwa [Function.update_of_ne hj] at this
        simp [Function.update_of_ne hj, pureProfile, this]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · have : ∃ j, j ≠ i ∧ s' j ≠ s j := by
        by_contra hcon
        push Not at hcon
        apply h
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · rw [Function.update_of_ne hj]; exact hcon j hj
      obtain ⟨j, hj, hne⟩ := this
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [Function.update_of_ne hj, pureProfile, hne]
  have hinner : ∀ s' : ∀ j, S j,
      (∑ a, if s' = Function.update s i a then τ a * u k s' else 0)
        = (if s' = Function.update s i (s' i) then τ (s' i) else 0) * u k s' := by
    intro s'
    rw [Finset.sum_eq_single (s' i)]
    · split_ifs <;> simp
    · intro a _ ha
      have hne : s' ≠ Function.update s i a := fun h => ha (by rw [h]; simp)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  calc mixedPayoff u (Function.update (pureProfile s) i τ) k
      = ∑ s' : ∀ j, S j, (if s' = Function.update s i (s' i) then τ (s' i) else 0) * u k s' := by
        simp only [mixedPayoff, hprod]
    _ = ∑ s' : ∀ j, S j, ∑ a, if s' = Function.update s i a then τ a * u k s' else 0 := by
        simp only [hinner]
    _ = ∑ a, ∑ s' : ∀ j, S j, if s' = Function.update s i a then τ a * u k s' else 0 :=
        Finset.sum_comm
    _ = ∑ a, τ a * u k (Function.update s i a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_ite_eq' Finset.univ (Function.update s i a)]
        simp

/-- The expected payoff at a pure profile is the payoff of that profile. -/
lemma mixedPayoff_pureProfile [DecidableEq ι] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ j, S j) → ℝ) (s : ∀ j, S j) (k : ι) :
    mixedPayoff u (pureProfile s) k = u k s := by
  have h := mixedPayoff_update_pureProfile u s k (pureProfile s k) k
  rw [Function.update_eq_self] at h
  rw [h]
  simp [pureProfile, Pi.single_apply]

/-- A pure profile is a mixed Nash equilibrium (as a degenerate mixed profile) iff it is a pure
Nash equilibrium. -/
theorem isMixedNash_pure_iff [DecidableEq ι] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ j, S j) → ℝ) (s : ∀ j, S j) :
    IsMixedNash u (pureProfile s) ↔ IsPureNash u s := by
  constructor
  · rintro ⟨-, h⟩ i a
    have := h i _ (single_mem_mixedStrategies a)
    rw [mixedPayoff_update_pureProfile, mixedPayoff_pureProfile] at this
    simpa [Pi.single_apply] using this
  · intro h
    refine ⟨fun i => single_mem_mixedStrategies (s i), fun i τ hτ => ?_⟩
    rw [mixedPayoff_update_pureProfile, mixedPayoff_pureProfile]
    calc ∑ a, τ a * u i (Function.update s i a) ≤ ∑ a, τ a * u i s :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h i a) (hτ.1 a)
      _ = u i s := by rw [← Finset.sum_mul, hτ.2, one_mul]

/-- Finite games with a generalized ordinal potential have a mixed Nash equilibrium (a pure
one). -/
theorem exists_isMixedNash_of_potential [DecidableEq ι] [∀ i, Nonempty (S i)]
    (u : ι → (∀ j, S j) → ℝ) (Φ : (∀ j, S j) → ℝ) (hΦ : IsGeneralizedOrdinalPotential u Φ) :
    ∃ σ, IsMixedNash u σ := by
  classical
  obtain ⟨s, hs⟩ := exists_isPureNash_of_potential u Φ hΦ
  exact ⟨pureProfile s, (isMixedNash_pure_iff u s).mpr hs⟩

end Strategic

end Applied.Economics
