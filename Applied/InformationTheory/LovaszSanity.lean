import Applied.InformationTheory.LovaszOddCycle
import Applied.InformationTheory.ShannonCapacityC7

/-!
# Sanity checks for the Lovász odd-cycle bound and the `C₇` bounds

Adversarial-review checks of `shannonCapacity_cycleGraph_odd_le`
(`Θ(Cₙ) ≤ n cos(π/n)/(1 + cos(π/n))` for odd `n ≥ 3`):

* the bound is attained at `n = 3` (`shannonCapacity_cycleGraph_three`: `Θ(C₃) = 1`) and its
  value at `n = 5` is `√5` (`oddCycleBound_five`), so the general theorem contains `Θ(C₅) ≤ √5`;
* both hypotheses are needed: the inequality is false for `n = 4`
  (`not_bound_cycleGraph_four`), for `n = 2` (`not_bound_cycleGraph_two`) and for `n = 1`
  (`not_bound_cycleGraph_one`, where the right-hand side is the junk value `(-1)/0 = 0`);
* the two bounds on `Θ(C₇)` leave a nonempty window strictly inside the trivial bounds
  `α(C₇) = 3` and Shannon's `7/2` (`shannonCapacity_cycleGraph_seven_window`);
* junk value of the definition: on an infinite vertex type `shannonCapacity` can be `0`
  (`shannonCapacity_bot_nat`), which is why every theorem assumes `Fintype V`.
-/

open Real

namespace Applied.InformationTheory.LovaszSanity

/-- `1 ≤ Θ(G)` for a finite graph with a vertex. -/
theorem one_le_shannonCapacity {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    (1 : ℝ) ≤ shannonCapacity G := by
  classical
  have hind : G.IsIndepSet (({Classical.arbitrary V} : Finset V) : Set V) := by
    simp [SimpleGraph.IsIndepSet]
  have h : 1 ≤ G.indepNum := by simpa using hind.card_le_indepNum
  exact le_trans (by exact_mod_cast h) (indepNum_le_shannonCapacity G)

/-- The bound is attained for the triangle: `Θ(C₃) = 1 = 3 cos(π/3)/(1 + cos(π/3))`. -/
theorem shannonCapacity_cycleGraph_three :
    shannonCapacity (SimpleGraph.cycleGraph 3) = 1 := by
  refine le_antisymm ?_ (one_le_shannonCapacity _)
  have h := shannonCapacity_cycleGraph_odd_le 3 le_rfl ⟨1, rfl⟩
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3, cos_pi_div_three] at h
  norm_num at h
  exact h

/-- At `n = 5` the bound is `√5`: the odd-cycle theorem contains Lovász's `Θ(C₅) ≤ √5`. -/
theorem oddCycleBound_five : 5 * cos (π / 5) / (1 + cos (π / 5)) = √5 := by
  rw [cos_pi_div_five]
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 < √5 := by positivity
  rw [div_eq_iff (by positivity)]
  nlinarith

/-- Oddness is needed: for `C₄`, `Θ = 2` exceeds `4 cos(π/4)/(1 + cos(π/4)) ≈ 1.657`. -/
theorem not_bound_cycleGraph_four :
    ¬ shannonCapacity (SimpleGraph.cycleGraph 4) ≤ 4 * cos (π / 4) / (1 + cos (π / 4)) := by
  have hind : (SimpleGraph.cycleGraph 4).IsIndepSet (({0, 2} : Finset (Fin 4)) : Set _) := by
    intro i hi j hj hij hadj
    rw [SimpleGraph.cycleGraph_adj] at hadj
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi hj
    revert i j
    decide
  have h2 : 2 ≤ (SimpleGraph.cycleGraph 4).indepNum := hind.card_le_indepNum
  have h2' : (2 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 4) :=
    le_trans (by exact_mod_cast h2) (indepNum_le_shannonCapacity _)
  intro h
  have hc : cos (π / 4) < 1 := by
    rw [cos_pi_div_four]
    have : √2 < 2 := by
      nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith
  have hc0 : 0 < cos (π / 4) := by rw [cos_pi_div_four]; positivity
  have := h2'.trans h
  rw [le_div_iff₀ (by linarith)] at this
  linarith

/-- `n ≥ 3` is needed: Mathlib's `cycleGraph 2` is an edge, `Θ = 1`, and the formula gives `0`. -/
theorem not_bound_cycleGraph_two :
    ¬ shannonCapacity (SimpleGraph.cycleGraph 2) ≤ 2 * cos (π / 2) / (1 + cos (π / 2)) := by
  have := one_le_shannonCapacity (SimpleGraph.cycleGraph 2)
  rw [cos_pi_div_two]
  norm_num
  linarith

/-- `n ≥ 3` is needed: `cycleGraph 1` is a point, `Θ = 1`, and the formula is the junk value
`1 · (-1) / (1 + (-1)) = (-1)/0 = 0`. -/
theorem not_bound_cycleGraph_one :
    ¬ shannonCapacity (SimpleGraph.cycleGraph 1) ≤ 1 * cos (π / 1) / (1 + cos (π / 1)) := by
  have := one_le_shannonCapacity (SimpleGraph.cycleGraph 1)
  simp only [div_one, cos_pi]
  norm_num
  linarith

/-- The proved window for `Θ(C₇)`: strictly above `α(C₇) = 3` (indeed above `13/4`), and
strictly below Shannon's fractional bound `7/2` (indeed below `3.3177`). -/
theorem shannonCapacity_cycleGraph_seven_window :
    (13 / 4 : ℝ) < shannonCapacity (SimpleGraph.cycleGraph 7) ∧
      shannonCapacity (SimpleGraph.cycleGraph 7) < 3.3177 :=
  ⟨thirteen_fourths_lt_shannonCapacity_cycleGraph_seven,
    lt_of_le_of_lt shannonCapacity_cycleGraph_seven_le (by norm_num)⟩

/-- The two headline bounds are consistent: `367^{1/5} ≤ 7 cos(π/7)/(1 + cos(π/7))`. -/
theorem lower_le_upper :
    (367 : ℝ) ^ ((1 : ℝ) / 5) ≤ 7 * cos (π / 7) / (1 + cos (π / 7)) :=
  rpow_threeHundredSixtySeven_le_shannonCapacity_cycleGraph_seven.trans
    shannonCapacity_cycleGraph_seven_le_lovaszTheta

/-- Junk value: Mathlib's `indepNum` is `0` for the edgeless graph on `ℕ` (the supremum of an
unbounded set of naturals), although every finite set is independent. -/
theorem indepNum_strongPow_bot_nat (k : ℕ) :
    (strongPow (⊥ : SimpleGraph ℕ) (k + 1)).indepNum = 0 := by
  classical
  unfold SimpleGraph.indepNum
  refine Nat.sSup_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  let s : Finset (Fin (k + 1) → ℕ) := (Finset.range (B + 1)).image fun m _ => m
  have hinj : Function.Injective fun (m : ℕ) (_ : Fin (k + 1)) => m := fun a b h => congrFun h 0
  have hs : (strongPow (⊥ : SimpleGraph ℕ) (k + 1)).IsNIndepSet (B + 1) s := by
    refine ⟨fun f _ g _ hfg hadj => hfg (funext fun i => ?_), ?_⟩
    · rcases hadj.2 i with h | h
      · exact h
      · exact (h : False).elim
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have := hB ⟨s, hs⟩
  omega

/-- Junk value: for the edgeless graph on `ℕ` (infinitely many pairwise distinguishable
letters) the definition returns `Θ = 0`. All theorems of the library assume `Fintype V`. -/
theorem shannonCapacity_bot_nat : shannonCapacity (⊥ : SimpleGraph ℕ) = 0 := by
  unfold shannonCapacity
  have h : ∀ k : ℕ, ((strongPow (⊥ : SimpleGraph ℕ) (k + 1)).indepNum : ℝ) ^
      (((k + 1 : ℕ) : ℝ)⁻¹) = 0 := fun k => by
    rw [indepNum_strongPow_bot_nat, Nat.cast_zero, Real.zero_rpow (by positivity)]
  simp only [h]
  exact ciSup_const

end Applied.InformationTheory.LovaszSanity
