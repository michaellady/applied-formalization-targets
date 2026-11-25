import Applied.InformationTheory.ErasureEndpoints

/-!
# Achievability for zero-error-decodable channels; the binary symmetric channel at `q = 0, 1/2, 1`

All logarithms are natural.

* `achievable_memoryless_of_decodable`: if a single-letter channel `W : X → Y → ℝ` (finite
  nonempty `X`) admits a letter decoder `g : Y → X` with `W x y ≠ 0 → g y = x`, then the rate
  `log |X|` is achievable over `memoryless W` (with maximal error exactly `0`), and
  `opCapacity_memoryless_of_decodable`: if moreover `W` is row-stochastic,
  `opCapacity (memoryless W) = log |X|`.
* `opCapacity_memoryless_bsc_zero`, `opCapacity_memoryless_bsc_one`: `log 2`.
* `opCapacity_memoryless_bsc_half`: `0`.
* `opCapacity_memoryless_bsc_eq_capacity_of_endpoint`: for `q ∈ {0, 1/2, 1}`,
  `opCapacity (memoryless (bsc q)) = capacity (bsc q) = log 2 - h(q)`.
-/

open Finset Real

namespace Applied.InformationTheory

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- The code using all `|X|ⁿ` words, decoded letter by letter with `g`. -/
noncomputable def decodableCode (W : X → Y → ℝ) (g : Y → X) (n : ℕ) :
    BlockCode (memoryless W) n (Fintype.card (Fin n → X)) where
  enc := (Fintype.equivFin (Fin n → X)).symm
  dec y := Fintype.equivFin (Fin n → X) (fun i => g ((y : Fin n → Y) i))

lemma decodableCode_errorProb {W : X → Y → ℝ} {g : Y → X} (hg : ∀ x y, W x y ≠ 0 → g y = x)
    (n : ℕ) (m : Fin (Fintype.card (Fin n → X))) : (decodableCode W g n).errorProb m = 0 := by
  classical
  refine Finset.sum_eq_zero fun y _ => ?_
  split_ifs with hdec
  · rfl
  · change ∏ i, W ((Fintype.equivFin (Fin n → X)).symm m i) ((y : Fin n → Y) i) = 0
    by_cases hall : ∀ i, W ((Fintype.equivFin (Fin n → X)).symm m i) ((y : Fin n → Y) i) ≠ 0
    · exfalso
      apply hdec
      change Fintype.equivFin (Fin n → X) (fun i => g ((y : Fin n → Y) i)) = m
      have : (fun i => g ((y : Fin n → Y) i)) = (Fintype.equivFin (Fin n → X)).symm m := by
        funext i; exact hg _ _ (hall i)
      rw [this, Equiv.apply_symm_apply]
    · simp only [not_forall, not_not] at hall
      obtain ⟨i, hi⟩ := hall
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- **Achievability for zero-error-decodable channels.** If every output letter of positive
(nonzero) probability determines the input letter through `g`, the rate `log |X|` is
achievable over the memoryless channel; the code of all words has maximal error `0`. -/
theorem achievable_memoryless_of_decodable [Nonempty X] {W : X → Y → ℝ} {g : Y → X}
    (hg : ∀ x y, W x y ≠ 0 → g y = x) :
    Achievable (memoryless W) (log (Fintype.card X)) := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨_, decodableCode W g n, ?_, ?_⟩⟩
  · rw [Fintype.card_fun, Fintype.card_fin, Real.exp_nat_mul,
      Real.exp_log (by exact_mod_cast Fintype.card_pos)]
    push_cast; exact le_rfl
  · exact Real.iSup_le (fun m => (decodableCode_errorProb hg n m).le.trans hε.le) hε.le

/-- For a row-stochastic zero-error-decodable channel, the operational capacity is
`log |X|`. -/
theorem opCapacity_memoryless_of_decodable [Nonempty X] {W : X → Y → ℝ} (hW : IsChannel W)
    {g : Y → X} (hg : ∀ x y, W x y ≠ 0 → g y = x) :
    opCapacity (memoryless W) = log (Fintype.card X) :=
  le_antisymm (opCapacity_le_log_card (isStochastic_memoryless hW))
    (le_opCapacity (isStochastic_memoryless hW) (achievable_memoryless_of_decodable hg))

/-- The noiseless binary symmetric channel has operational capacity `log 2`. -/
theorem opCapacity_memoryless_bsc_zero : opCapacity (memoryless (bsc 0)) = log 2 := by
  have := opCapacity_memoryless_of_decodable (isChannel_bsc (q := 0) le_rfl zero_le_one)
    (g := id) (fun x y h => by
      by_contra hne
      have : x ≠ y := fun hxy => hne hxy.symm
      exact h (by simp [bsc, this]))
  simpa using this

/-- The binary symmetric channel that always flips has operational capacity `log 2`. -/
theorem opCapacity_memoryless_bsc_one : opCapacity (memoryless (bsc 1)) = log 2 := by
  have := opCapacity_memoryless_of_decodable (isChannel_bsc (q := 1) zero_le_one le_rfl)
    (g := fun b => !b) (fun x y h => by
      by_contra hne
      apply h
      have : x = y := by cases x <;> cases y <;> simp_all
      simp [bsc, this])
  simpa using this

/-- The binary symmetric channel with crossover probability `1/2` has operational capacity
`0`. -/
theorem opCapacity_memoryless_bsc_half : opCapacity (memoryless (bsc 2⁻¹)) = 0 := by
  have hF := isStochastic_memoryless (isChannel_bsc (q := 2⁻¹) (by norm_num) (by norm_num))
  refine opCapacity_eq_zero_of_const hF fun n x x' => ?_
  have hrow : ∀ b b' : Bool, bsc 2⁻¹ b = bsc 2⁻¹ b' := fun b b' => by
    funext y; unfold bsc; split_ifs <;> norm_num
  funext y
  change ∏ i, bsc 2⁻¹ (x i) (y i) = ∏ i, bsc 2⁻¹ (x' i) (y i)
  exact Finset.prod_congr rfl fun i _ => by rw [hrow (x i) (x' i)]

/-- **The channel coding theorem for the binary symmetric channel at `q ∈ {0, 1/2, 1}`.** -/
theorem opCapacity_memoryless_bsc_eq_capacity_of_endpoint {q : ℝ}
    (hq : q = 0 ∨ q = 2⁻¹ ∨ q = 1) :
    opCapacity (memoryless (bsc q)) = capacity (bsc q) ∧
      capacity (bsc q) = log 2 - binEntropy q := by
  rcases hq with rfl | rfl | rfl
  · rw [capacity_bsc 0 le_rfl zero_le_one, opCapacity_memoryless_bsc_zero]; simp
  · rw [capacity_bsc 2⁻¹ (by norm_num) (by norm_num), opCapacity_memoryless_bsc_half]; simp
  · rw [capacity_bsc 1 zero_le_one le_rfl, opCapacity_memoryless_bsc_one]; simp

end Applied.InformationTheory
