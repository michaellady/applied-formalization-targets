import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Strong graph powers and the Shannon (zero-error) capacity of a graph

For a channel with confusability graph `G` (two input letters are adjacent when some output
can arise from both), the words of length `k` that can be confused are the adjacent vertices of
the `k`-th strong power of `G`, so the largest zero-error code of length `k` has
`α(G^{⊠k})` words, `α` the independence number.

* `strongPow G k`: the `k`-fold strong power of `G`, on `Fin k → V`: two distinct words are
  adjacent when in every coordinate the letters are equal or adjacent.
* `shannonCapacity G = sup_{k ≥ 1} α(G^{⊠k})^{1/k}` (a real number; Shannon's `Θ(G)`).
* `indepNum_strongPow_le`: `α(G^{⊠k}) ≤ |V|^k`.
* `le_shannonCapacity`: `α(G^{⊠k})^{1/k} ≤ Θ(G)` for `k ≥ 1`.
* `indepNum_le_shannonCapacity`: `α(G) ≤ Θ(G)`; `shannonCapacity_le_card`: `Θ(G) ≤ |V|`.
* `five_le_indepNum_strongPow_cycleGraph_five`: `5 ≤ α(C₅ ⊠ C₅)` (Shannon's code), hence
  `sqrt_five_le_shannonCapacity_cycleGraph_five`: `√5 ≤ Θ(C₅)`.
* `three_le_shannonCapacity_cycleGraph_seven`: `3 ≤ Θ(C₇)`.

Mathlib has `SimpleGraph.indepNum` and `SimpleGraph.cycleGraph` but no strong product.
-/

open Finset

namespace Applied.InformationTheory

variable {V : Type*}

/-- The `k`-fold strong power of a graph `G`: the graph on words `Fin k → V` in which two
distinct words are adjacent when, in every coordinate, the two letters are equal or adjacent
in `G`. -/
def strongPow (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj f g := f ≠ g ∧ ∀ i, f i = g i ∨ G.Adj (f i) (g i)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => (h.2 i).imp Eq.symm fun h => h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma strongPow_adj {G : SimpleGraph V} {k : ℕ} {f g : Fin k → V} :
    (strongPow G k).Adj f g ↔ f ≠ g ∧ ∀ i, f i = g i ∨ G.Adj (f i) (g i) := Iff.rfl

/-- The Shannon capacity `Θ(G) = sup_{k ≥ 1} α(G^{⊠k})^{1/k}` of a graph, as a real number
(the supremum is indexed by `k + 1` for `k : ℕ`). For a finite graph the family is bounded by
`|V|`, see `le_shannonCapacity`. -/
noncomputable def shannonCapacity (G : SimpleGraph V) : ℝ :=
  ⨆ k : ℕ, ((strongPow G (k + 1)).indepNum : ℝ) ^ (((k + 1 : ℕ) : ℝ)⁻¹)

variable [Fintype V]

/-- The independence number of the `k`-th strong power is at most `|V|^k`. -/
theorem indepNum_strongPow_le (G : SimpleGraph V) (k : ℕ) :
    (strongPow G k).indepNum ≤ Fintype.card V ^ k := by
  classical
  obtain ⟨s, hs⟩ := (strongPow G k).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  exact (Finset.card_le_univ s).trans_eq (by simp)

lemma rpow_indepNum_strongPow_le (G : SimpleGraph V) (k : ℕ) :
    ((strongPow G (k + 1)).indepNum : ℝ) ^ (((k + 1 : ℕ) : ℝ)⁻¹) ≤ Fintype.card V := by
  have h : ((strongPow G (k + 1)).indepNum : ℝ) ≤ (Fintype.card V : ℝ) ^ (k + 1) := by
    exact_mod_cast indepNum_strongPow_le G (k + 1)
  calc ((strongPow G (k + 1)).indepNum : ℝ) ^ (((k + 1 : ℕ) : ℝ)⁻¹)
      ≤ ((Fintype.card V : ℝ) ^ (k + 1)) ^ (((k + 1 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h (by positivity)
    _ = Fintype.card V := Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (Nat.succ_ne_zero k)

lemma bddAbove_shannonCapacity (G : SimpleGraph V) :
    BddAbove (Set.range fun k : ℕ =>
      ((strongPow G (k + 1)).indepNum : ℝ) ^ (((k + 1 : ℕ) : ℝ)⁻¹)) :=
  ⟨Fintype.card V, by rintro _ ⟨k, rfl⟩; exact rpow_indepNum_strongPow_le G k⟩

/-- Zero-error codes of every length `k + 1` give lower bounds on the Shannon capacity. -/
theorem le_shannonCapacity (G : SimpleGraph V) (k : ℕ) :
    ((strongPow G (k + 1)).indepNum : ℝ) ^ (((k + 1 : ℕ) : ℝ)⁻¹) ≤ shannonCapacity G :=
  le_ciSup (bddAbove_shannonCapacity G) k

/-- `Θ(G) ≤ |V|`. -/
theorem shannonCapacity_le_card (G : SimpleGraph V) : shannonCapacity G ≤ Fintype.card V :=
  ciSup_le fun k => rpow_indepNum_strongPow_le G k

/-- `α(G) ≤ α(G^{⊠1})`: an independent set of `G` is an independent set of constant words. -/
theorem indepNum_le_indepNum_strongPow_one (G : SimpleGraph V) :
    G.indepNum ≤ (strongPow G 1).indepNum := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hinj : Function.Injective fun (v : V) (_ : Fin 1) => v := fun v w h => congrFun h 0
  have hind : (strongPow G 1).IsIndepSet (s.image fun (v : V) (_ : Fin 1) => v : Finset _) := by
    intro f hf g hg hfg hadj
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hf hg
    obtain ⟨v, hv, rfl⟩ := hf
    obtain ⟨w, hw, rfl⟩ := hg
    have hvw : v ≠ w := fun h => hfg (by rw [h])
    rcases hadj.2 0 with h | h
    · exact hvw h
    · exact hs.isIndepSet hv hw hvw h
  have := hind.card_le_indepNum
  rwa [Finset.card_image_of_injective _ hinj, hs.card_eq] at this

/-- `α(G) ≤ Θ(G)`. -/
theorem indepNum_le_shannonCapacity (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ shannonCapacity G := by
  have h := le_shannonCapacity G 0
  simp only [zero_add, Nat.cast_one, inv_one, Real.rpow_one] at h
  exact (Nat.cast_le.mpr (indepNum_le_indepNum_strongPow_one G)).trans h

/-- **Shannon's code for the pentagon**: the five words `(i, 2i)`, `i ∈ ℤ/5`, are pairwise
non-confusable, so `5 ≤ α(C₅ ⊠ C₅)`. -/
theorem five_le_indepNum_strongPow_cycleGraph_five :
    5 ≤ (strongPow (SimpleGraph.cycleGraph 5) 2).indepNum := by
  have hinj : Function.Injective fun i : Fin 5 => ![i, 2 * i] := fun i j h => by
    simpa using congrFun h 0
  have hind : (strongPow (SimpleGraph.cycleGraph 5) 2).IsIndepSet
      (univ.image fun i : Fin 5 => ![i, 2 * i] : Finset _) := by
    intro f hf g hg hfg hadj
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hf hg
    obtain ⟨i, -, rfl⟩ := hf
    obtain ⟨j, -, rfl⟩ := hg
    have hij : i ≠ j := fun h => hfg (by rw [h])
    have h0 := hadj.2 0
    have h1 := hadj.2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, SimpleGraph.cycleGraph_adj] at h0 h1
    clear hfg hadj
    revert i j
    decide
  have := hind.card_le_indepNum
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at this

/-- `√5 ≤ Θ(C₅)` (Shannon 1956; equality is Lovász's theorem, not formalized here). -/
theorem sqrt_five_le_shannonCapacity_cycleGraph_five :
    Real.sqrt 5 ≤ shannonCapacity (SimpleGraph.cycleGraph 5) := by
  have h := le_shannonCapacity (SimpleGraph.cycleGraph 5) 1
  refine le_trans ?_ h
  have h5 : (5 : ℝ) ≤ ((strongPow (SimpleGraph.cycleGraph 5) 2).indepNum : ℝ) := by
    exact_mod_cast five_le_indepNum_strongPow_cycleGraph_five
  rw [Real.sqrt_eq_rpow]
  calc (5 : ℝ) ^ ((1 : ℝ) / 2)
      ≤ ((strongPow (SimpleGraph.cycleGraph 5) 2).indepNum : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by norm_num) h5 (by norm_num)
    _ = _ := by norm_num

/-- `3 ≤ α(C₇)`: the vertices `0, 2, 4` are pairwise non-adjacent. -/
theorem three_le_indepNum_cycleGraph_seven : 3 ≤ (SimpleGraph.cycleGraph 7).indepNum := by
  have hind : (SimpleGraph.cycleGraph 7).IsIndepSet (({0, 2, 4} : Finset (Fin 7)) : Set _) := by
    intro i hi j hj hij hadj
    rw [SimpleGraph.cycleGraph_adj] at hadj
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi hj
    revert i j
    decide
  exact hind.card_le_indepNum

/-- `3 ≤ Θ(C₇)`. -/
theorem three_le_shannonCapacity_cycleGraph_seven :
    (3 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  le_trans (by exact_mod_cast three_le_indepNum_cycleGraph_seven)
    (indepNum_le_shannonCapacity _)

end Applied.InformationTheory
