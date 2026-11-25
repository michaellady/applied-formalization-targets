import Applied.Economics.EFXThree

/-!
# Sanity checks for the definition of EFX (`Applied.Economics.IsEFX`)

Adversarial-review file: fully proved checks that the definition used by `efx_exists_three` is
the strong form of EFX on complete allocations and is not trivially true.

* `efxNat`, `isEFX_natCast_iff`: for natural-number valuations `IsEFX` is equivalent to a
  decidable predicate, so it can be evaluated by the kernel.
* `card_efx_inst1`, `card_efx_inst2`: for two explicit instances with three agents and four
  goods, exactly `5` (resp. `6`) of the `81` complete allocations are EFX. The same numbers are
  produced by an independent brute-force enumeration (Python) using the definition of
  Chaudhury–Garg–Mehlhorn ("no agent strongly envies another").
* `exists_not_isEFX`: `IsEFX` is not always true.
* `weak_not_strong`: an allocation that satisfies the EFX inequality for every good the envious
  agent values positively, but is not `IsEFX`; so `IsEFX` is the strong form (often written
  EFX₀), in which zero-valued goods may be removed as well.
* `isEFX_nonneg_own`: `IsEFX` forces every agent to value each of their own goods
  non-negatively; `not_exists_isEFX_neg`: hence the non-negativity hypothesis of the existence
  theorems cannot be dropped for this definition.
* `efx_three_no_goods`, `efx_three_one_good`: degenerate instances (`m = 0`, `m = 1`).
* `isEFX_iff_noSE`: `IsEFX` for three agents in terms of the predicate `EFX3`/`NoSE` used in the
  core theorem `efx3_nondegenerate`.
-/

open Finset Function

namespace Applied.Economics.EFXSanity

/-- The decidable form of `IsEFX` for natural-number valuations. -/
def efxNat {n m : ℕ} (v : Fin n → Fin m → ℕ) (a : Fin m → Fin n) : Prop :=
  ∀ i j : Fin n, ∀ g : Fin m, a g = j →
    ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h

instance {n m : ℕ} (v : Fin n → Fin m → ℕ) : DecidablePred (efxNat v) := fun a => by
  unfold efxNat
  infer_instance

/-- `IsEFX` for the real valuation obtained from a natural-number valuation is `efxNat`. -/
theorem isEFX_natCast_iff {n m : ℕ} (v : Fin n → Fin m → ℕ) (a : Fin m → Fin n) :
    IsEFX (fun i g => (v i g : ℝ)) a ↔ efxNat v a := by
  unfold IsEFX efxNat
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun g =>
    imp_congr_right fun _ => ?_
  beta_reduce
  rw [← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_le]

/-- Instance 1: three agents, four goods. -/
def inst1 : Fin 3 → Fin 4 → ℕ := ![![3, 1, 2, 0], ![1, 3, 0, 2], ![2, 2, 1, 1]]

/-- Instance 2: three agents, four goods; every agent values the first good at `5`. -/
def inst2 : Fin 3 → Fin 4 → ℕ := ![![5, 0, 0, 1], ![5, 1, 0, 0], ![5, 0, 1, 0]]

/-- Exactly `5` of the `81` complete allocations of instance 1 are EFX. -/
theorem card_efx_inst1 : #{a : Fin 4 → Fin 3 | efxNat inst1 a} = 5 := by decide +kernel

/-- Exactly `6` of the `81` complete allocations of instance 2 are EFX. -/
theorem card_efx_inst2 : #{a : Fin 4 → Fin 3 | efxNat inst2 a} = 6 := by decide +kernel

/-- In real terms: instance 1 has an EFX allocation and an allocation that is not EFX. -/
theorem exists_not_isEFX :
    (∃ a : Fin 4 → Fin 3, IsEFX (fun i g => (inst1 i g : ℝ)) a) ∧
      ∃ a : Fin 4 → Fin 3, ¬ IsEFX (fun i g => (inst1 i g : ℝ)) a := by
  simp only [isEFX_natCast_iff]
  decide +kernel

/-- Three agents value two goods at `(1, 0)`. Giving both goods to agent `0` satisfies the EFX
inequality for every good that the envious agent values positively, but it is not `IsEFX`:
removing the zero-valued good from agent `0`'s bundle leaves a bundle worth `1 > 0` to the
others. So `IsEFX` is the strong form of EFX. -/
theorem weak_not_strong :
    ∃ (v : Fin 3 → Fin 2 → ℝ) (a : Fin 2 → Fin 3), (∀ i g, 0 ≤ v i g) ∧
      (∀ i j : Fin 3, ∀ g : Fin 2, a g = j → 0 < v i g →
        ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h) ∧ ¬ IsEFX v a := by
  refine ⟨fun i g => ((![![1, 0], ![1, 0], ![1, 0]] : Fin 3 → Fin 2 → ℕ) i g : ℝ),
    fun _ => 0, fun i g => Nat.cast_nonneg _, ?_, ?_⟩
  · intro i j g hg hpos
    have hg0 : g = 0 := by
      fin_cases g
      · rfl
      · exfalso; fin_cases i <;> simp at hpos
    subst hg0
    have : (univ.filter fun h : Fin 2 => (0 : Fin 3) = j ∧ h ≠ 0) ⊆ {1} := by
      intro h; fin_cases h <;> simp
    calc _ ≤ ∑ h ∈ ({1} : Finset (Fin 2)),
          ((![![1, 0], ![1, 0], ![1, 0]] : Fin 3 → Fin 2 → ℕ) i h : ℝ) :=
          sum_le_sum_of_subset_of_nonneg this fun _ _ _ => Nat.cast_nonneg _
      _ = 0 := by fin_cases i <;> simp
      _ ≤ _ := sum_nonneg fun _ _ => Nat.cast_nonneg _
  · rw [isEFX_natCast_iff]
    decide +kernel

variable {A G : Type*} [Fintype G] [DecidableEq A] [DecidableEq G]

/-- `IsEFX` (which also compares each agent with themself) forces every agent to value each of
their own goods non-negatively. -/
theorem isEFX_nonneg_own {v : A → G → ℝ} {a : G → A} (h : IsEFX v a) (g : G) :
    0 ≤ v (a g) g := by
  have h1 := h (a g) (a g) g rfl
  have h2 : ∑ h with a h = a g ∧ h ≠ g, v (a g) h + v (a g) g = ∑ h with a h = a g, v (a g) h := by
    have : (univ.filter fun h => a h = a g ∧ h ≠ g) = (univ.filter fun h => a h = a g).erase g := by
      ext h
      simp [and_comm]
    rw [this, sum_erase_add _ _ (by simp)]
  linarith

/-- The non-negativity hypothesis of the existence theorems cannot be dropped for `IsEFX`: if
every agent values the single good at `-1`, no allocation is `IsEFX`. -/
theorem not_exists_isEFX_neg :
    ¬ ∃ a : Fin 1 → Fin 3, IsEFX (fun (_ : Fin 3) (_ : Fin 1) => (-1 : ℝ)) a := by
  rintro ⟨a, h⟩
  have := isEFX_nonneg_own h 0
  norm_num at this

/-- With no goods the unique allocation is EFX. -/
theorem efx_three_no_goods (v : Fin 3 → Fin 0 → ℝ) (a : Fin 0 → Fin 3) : IsEFX v a :=
  fun _ _ g => g.elim0

/-- With one good of non-negative value every allocation is EFX. -/
theorem efx_three_one_good (v : Fin 3 → Fin 1 → ℝ) (hv : ∀ i g, 0 ≤ v i g) (a : Fin 1 → Fin 3) :
    IsEFX v a := by
  intro i j g _
  have : (univ.filter fun h : Fin 1 => a h = j ∧ h ≠ g) = ∅ := by
    ext h
    simp [Subsingleton.elim h g]
  rw [this, sum_empty]
  exact sum_nonneg fun h _ => hv i h

/-- `IsEFX` for three agents, in terms of the predicate `NoSE` ("no strong envy") of the core
theorem: with `X k` the bundle of agent `k`, the allocation is `IsEFX` iff
`NoSE (v i) (X i) (X j)` for all `i`, `j`. -/
theorem isEFX_iff_noSE (v : A → G → ℝ) (a : G → A) :
    IsEFX v a ↔ ∀ i j : A, NoSE (v i) (univ.filter fun h => a h = i) (univ.filter fun h => a h = j) := by
  have key : ∀ (j : A) (g : G), (univ.filter fun h => a h = j ∧ h ≠ g) =
      (univ.filter fun h => a h = j).erase g := by
    intro j g
    ext h
    simp [and_comm]
  constructor
  · intro h i j g hg
    rw [← key]
    exact h i j g (by simpa using hg)
  · intro h i j g hg
    rw [key]
    exact h i j g (by simpa using hg)

end Applied.Economics.EFXSanity
