import Mathlib.Topology.Sion
import Mathlib.Tactic

/-!
# Von Neumann's minimax theorem for finite zero-sum games

A two-player zero-sum game is given by a real payoff matrix `A : Matrix m n ℝ` (finite,
nonempty index types). A mixed strategy over a finite set `m` of pure strategies is a
probability vector `p ∈ mixedStrategies m`, i.e. `p : m → ℝ` with non-negative entries summing
to `1`. (This set is definitionally Mathlib's `stdSimplex ℝ m`, which is deprecated in the
pinned Mathlib in favour of a bundled type, so it is defined here directly.) The row player
chooses a mixed strategy `p ∈ mixedStrategies m` and wants
to maximise the expected payoff `p ⬝ᵥ A *ᵥ q`; the column player chooses `q ∈ mixedStrategies n`
and wants to minimise it.

Mathlib proves Sion's minimax theorem (`Sion.exists_isSaddlePointOn` in
`Mathlib/Topology/Sion.lean`) and lists the matrix-game case as a TODO; this file spells that
special case out.

* `exists_saddle_point`: there are mixed strategies `p`, `q` with
  `p' ⬝ᵥ A *ᵥ q ≤ p ⬝ᵥ A *ᵥ q ≤ p ⬝ᵥ A *ᵥ q'` for all mixed `p'`, `q'` (a Nash equilibrium).
* `exists_value`: there is a value `v` that the row player can guarantee at least and the
  column player can guarantee at most; `value_unique` shows weak duality, so `v` is unique.
* `exists_value_pure`: the same, tested against pure strategies only.
* `iSup_iInf_eq_iInf_iSup`: `max_p min_q pᵀAq = min_q max_p pᵀAq` as an identity between
  suprema and infima over the simplices.
-/

open Matrix Set

namespace Applied.Economics

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The mixed strategies over a finite set `m` of pure strategies: probability vectors. -/
def mixedStrategies (m : Type*) [Fintype m] : Set (m → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- A pure strategy, as a mixed strategy. -/
lemma single_mem_mixedStrategies [DecidableEq m] (i : m) :
    Pi.single i (1 : ℝ) ∈ mixedStrategies m :=
  ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩

lemma mixedStrategies_nonempty [Nonempty m] : (mixedStrategies m).Nonempty := by
  classical
  exact ⟨_, single_mem_mixedStrategies (Classical.arbitrary m)⟩

lemma convex_mixedStrategies : Convex ℝ (mixedStrategies m) := by
  rintro f ⟨hf0, hf1⟩ g ⟨hg0, hg1⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hf0 i)) (mul_nonneg hb (hg0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hf1, hg1, mul_one, hab]

lemma isCompact_mixedStrategies : IsCompact (mixedStrategies m) := by
  have hcl : IsClosed (mixedStrategies m) := by
    have : mixedStrategies m = (⋂ i, {p : m → ℝ | 0 ≤ p i}) ∩ {p | ∑ i, p i = 1} := by
      ext p
      simp [mixedStrategies]
    rw [this]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : m → ℝ)) (b := 1)) hcl ?_
  rintro p ⟨hp0, hp1⟩
  refine ⟨fun i => hp0 i, fun i => ?_⟩
  change p i ≤ 1
  rw [← hp1]
  exact Finset.single_le_sum (f := p) (fun j _ => hp0 j) (Finset.mem_univ i)

/-- Expected payoff to the row player when the row player mixes with `p` and the column player
with `q`. -/
def gamePayoff (A : Matrix m n ℝ) (p : m → ℝ) (q : n → ℝ) : ℝ := p ⬝ᵥ A *ᵥ q

lemma gamePayoff_eq_sum (A : Matrix m n ℝ) (p : m → ℝ) (q : n → ℝ) :
    gamePayoff A p q = ∑ i, ∑ j, p i * A i j * q j := by
  simp only [gamePayoff, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

lemma continuous_gamePayoff_left (A : Matrix m n ℝ) (q : n → ℝ) :
    Continuous fun p : m → ℝ => gamePayoff A p q := by
  simp only [gamePayoff_eq_sum]
  fun_prop

lemma continuous_gamePayoff_right (A : Matrix m n ℝ) (p : m → ℝ) :
    Continuous fun q : n → ℝ => gamePayoff A p q := by
  simp only [gamePayoff_eq_sum]
  fun_prop

lemma gamePayoff_combo_left (A : Matrix m n ℝ) (p p' : m → ℝ) (q : n → ℝ) (a b : ℝ) :
    gamePayoff A (a • p + b • p') q = a * gamePayoff A p q + b * gamePayoff A p' q := by
  simp [gamePayoff, add_dotProduct, smul_dotProduct]

lemma gamePayoff_combo_right (A : Matrix m n ℝ) (p : m → ℝ) (q q' : n → ℝ) (a b : ℝ) :
    gamePayoff A p (a • q + b • q') = a * gamePayoff A p q + b * gamePayoff A p q' := by
  simp [gamePayoff, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul]

/-- **Von Neumann's minimax theorem, saddle-point form.** Every finite zero-sum game has a
pair of optimal mixed strategies: neither player can gain by deviating. -/
theorem exists_saddle_point [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) :
    ∃ p ∈ mixedStrategies m, ∃ q ∈ mixedStrategies n,
      (∀ p' ∈ mixedStrategies m, gamePayoff A p' q ≤ gamePayoff A p q) ∧
      (∀ q' ∈ mixedStrategies n, gamePayoff A p q ≤ gamePayoff A p q') := by
  classical
  have neM : (mixedStrategies m).Nonempty :=
    ⟨_, single_mem_mixedStrategies (Classical.arbitrary m)⟩
  have neN : (mixedStrategies n).Nonempty :=
    ⟨_, single_mem_mixedStrategies (Classical.arbitrary n)⟩
  obtain ⟨q, hq, p, hp, hsad⟩ := Sion.exists_isSaddlePointOn
    (X := mixedStrategies n) (Y := mixedStrategies m) (f := fun q p => gamePayoff A p q)
    neN (convex_mixedStrategies) isCompact_mixedStrategies
    (fun p _ => (continuous_gamePayoff_right A p).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun p _ => ConvexOn.quasiconvexOn ⟨convex_mixedStrategies, fun x _ y _ a b _ _ _ => by
      simp only [gamePayoff_combo_right, smul_eq_mul, le_refl]⟩)
    (convex_mixedStrategies) neM isCompact_mixedStrategies
    (fun q _ => (continuous_gamePayoff_left A q).upperSemicontinuous.upperSemicontinuousOn _)
    (fun q _ => ConcaveOn.quasiconcaveOn ⟨convex_mixedStrategies, fun x _ y _ a b _ _ _ => by
      simp only [gamePayoff_combo_left, smul_eq_mul, le_refl]⟩)
  exact ⟨p, hp, q, hq, fun p' hp' => hsad q hq p' hp', fun q' hq' => hsad q' hq' p hp⟩

/-- **Minimax theorem, value form.** There is a number `v` (the value of the game) such that
the row player has a mixed strategy guaranteeing expected payoff at least `v` and the column
player has a mixed strategy guaranteeing expected payoff at most `v`. -/
theorem exists_value [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) :
    ∃ v : ℝ, (∃ p ∈ mixedStrategies m, ∀ q ∈ mixedStrategies n, v ≤ gamePayoff A p q) ∧
      (∃ q ∈ mixedStrategies n, ∀ p ∈ mixedStrategies m, gamePayoff A p q ≤ v) := by
  obtain ⟨p, hp, q, hq, h1, h2⟩ := exists_saddle_point A
  exact ⟨gamePayoff A p q, ⟨p, hp, h2⟩, ⟨q, hq, h1⟩⟩

/-- Weak duality: what the row player can guarantee never exceeds what the column player can
guarantee. Hence the value in `exists_value` is unique. -/
theorem value_unique (A : Matrix m n ℝ) {v₁ v₂ : ℝ}
    (h₁ : ∃ p ∈ mixedStrategies m, ∀ q ∈ mixedStrategies n, v₁ ≤ gamePayoff A p q)
    (h₂ : ∃ q ∈ mixedStrategies n, ∀ p ∈ mixedStrategies m, gamePayoff A p q ≤ v₂) : v₁ ≤ v₂ := by
  obtain ⟨p, hp, hp'⟩ := h₁
  obtain ⟨q, hq, hq'⟩ := h₂
  exact (hp' q hq).trans (hq' p hp)

/-- **Minimax theorem, pure-strategy test form.** There are a value `v` and mixed strategies
`p`, `q` such that `p` earns at least `v` against every column and `q` concedes at most `v`
against every row. -/
theorem exists_value_pure [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n]
    (A : Matrix m n ℝ) :
    ∃ v : ℝ, ∃ p ∈ mixedStrategies m, ∃ q ∈ mixedStrategies n,
      (∀ j, v ≤ ∑ i, p i * A i j) ∧ (∀ i, ∑ j, A i j * q j ≤ v) := by
  obtain ⟨p, hp, q, hq, h1, h2⟩ := exists_saddle_point A
  refine ⟨gamePayoff A p q, p, hp, q, hq, fun j => ?_, fun i => ?_⟩
  · have h := h2 _ (single_mem_mixedStrategies j)
    simpa [gamePayoff, dotProduct, mulVec, Pi.single_apply] using h
  · have h := h1 _ (single_mem_mixedStrategies i)
    simpa [gamePayoff, dotProduct, mulVec, Pi.single_apply] using h

/-- **Minimax theorem, `sup inf = inf sup` form.** The suprema and infima range over the
probability simplices (as subtypes); they are attained, by `exists_saddle_point`. -/
theorem iSup_iInf_eq_iInf_iSup [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) :
    ⨆ p : mixedStrategies m, ⨅ q : mixedStrategies n, gamePayoff A p q
      = ⨅ q : mixedStrategies n, ⨆ p : mixedStrategies m, gamePayoff A p q := by
  classical
  obtain ⟨p₀, hp₀, q₀, hq₀, h1, h2⟩ := exists_saddle_point A
  have : Nonempty (mixedStrategies m) := ⟨⟨p₀, hp₀⟩⟩
  have : Nonempty (mixedStrategies n) := ⟨⟨q₀, hq₀⟩⟩
  set v := gamePayoff A p₀ q₀
  have bddB : ∀ p : m → ℝ, BddBelow (range fun q : mixedStrategies n => gamePayoff A p q) := by
    intro p
    have hc := ((isCompact_mixedStrategies (m := n)).image (continuous_gamePayoff_right A p)).bddBelow
    refine hc.mono ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨q, q.2, rfl⟩
  have bddA : ∀ q : n → ℝ, BddAbove (range fun p : mixedStrategies m => gamePayoff A p q) := by
    intro q
    have hc := ((isCompact_mixedStrategies (m := m)).image (continuous_gamePayoff_left A q)).bddAbove
    refine hc.mono ?_
    rintro _ ⟨p, rfl⟩
    exact ⟨p, p.2, rfl⟩
  have hinf_le : ∀ p : mixedStrategies m, ⨅ q : mixedStrategies n, gamePayoff A p q ≤ v :=
    fun p => (ciInf_le (bddB p) ⟨q₀, hq₀⟩).trans (h1 p p.2)
  have hle_sup : ∀ q : mixedStrategies n, v ≤ ⨆ p : mixedStrategies m, gamePayoff A p q :=
    fun q => (h2 q q.2).trans (le_ciSup (bddA q) ⟨p₀, hp₀⟩)
  have e1 : ⨆ p : mixedStrategies m, ⨅ q : mixedStrategies n, gamePayoff A p q = v := by
    apply le_antisymm (ciSup_le hinf_le)
    refine le_trans ?_ (le_ciSup (f := fun p : mixedStrategies m =>
      ⨅ q : mixedStrategies n, gamePayoff A p q) ⟨v, ?_⟩ ⟨p₀, hp₀⟩)
    · exact le_ciInf fun q => h2 q q.2
    · rintro _ ⟨p, rfl⟩
      exact hinf_le p
  have e2 : ⨅ q : mixedStrategies n, ⨆ p : mixedStrategies m, gamePayoff A p q = v := by
    apply le_antisymm _ (le_ciInf hle_sup)
    refine le_trans (ciInf_le (f := fun q : mixedStrategies n =>
      ⨆ p : mixedStrategies m, gamePayoff A p q) ⟨v, ?_⟩ ⟨q₀, hq₀⟩) ?_
    · rintro _ ⟨q, rfl⟩
      exact hle_sup q
    · exact ciSup_le fun p => h1 p p.2
  rw [e1, e2]

end Applied.Economics
