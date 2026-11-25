import Applied.Complexity.PolyTime
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

/-!
# Randomized polynomial-time algorithms and the planted clique distributions

* `RandAlg`: a randomized algorithm on bit strings, given by a deterministic function of the
  input and of a string of coin tosses, and a polynomial giving the number of coins as a
  function of the input length. `RandAlg.IsPolyTime`: the deterministic function is
  polynomial-time computable (Turing machine, `Applied/Complexity/PolyTime.lean`).
* `RandAlg.acceptProb A x`: the probability, over uniform coins, that `A` outputs `1` on `x`.
* `sampleAdj w`: the graph on `Fin n` whose edge `{i, j}`, `i < j`, is present iff `w i j`;
  for uniform `w : Fin n → Fin n → Bool` this is the Erdős–Rényi graph `G(n, 1/2)`.
* `plantedAdj w S`: the same graph with all pairs inside `S` joined (a planted clique on `S`).
* `probNull A n`, `probPlanted A n k`: the probability that `A` accepts the adjacency matrix of
  `G(n, 1/2)`, respectively of `G(n, 1/2)` with a clique planted on a uniformly random
  `k`-subset.
* `advantage A n k`: the absolute difference of the two.
* Sanity: `acceptProb` lies in `[0, 1]`; planting a clique on at most one vertex changes
  nothing, so `advantage A n k = 0` for `k ≤ 1`; constant algorithms are polynomial time.
-/

open Finset

namespace Applied.Complexity

/-- A randomized algorithm on bit strings: on input `x` it draws `coins.eval |x|` uniform bits
`ρ` and outputs `run x ρ`. -/
structure RandAlg where
  /-- the output as a function of the input and of the coins -/
  run : List Bool → List Bool → Bool
  /-- the number of coins, as a polynomial in the input length -/
  coins : Polynomial ℕ

namespace RandAlg

/-- The algorithm runs in polynomial time: `(x, ρ) ↦ run x ρ` is polynomial-time computable,
the pair being written as the self-delimiting form `sd x` of `x` followed by `ρ`. Since the
number of coins is polynomial in `|x|`, this is polynomial time in `|x|`. -/
def IsPolyTime (A : RandAlg) : Prop :=
  PolyTimeComputable (fun p : List Bool × List Bool => sd p.1 ++ p.2) Computability.encodeBool
    (fun p => A.run p.1 p.2)

/-- The probability that `A` outputs `1` on input `x`, over uniform coins. -/
noncomputable def acceptProb (A : RandAlg) (x : List Bool) : ℝ :=
  ((univ.filter fun ρ : Fin (A.coins.eval x.length) → Bool =>
      A.run x (List.ofFn ρ) = true).card : ℝ) / 2 ^ A.coins.eval x.length

/-- The acceptance probability is non-negative. -/
theorem acceptProb_nonneg (A : RandAlg) (x : List Bool) : 0 ≤ A.acceptProb x := by
  unfold acceptProb; positivity

/-- The acceptance probability is at most `1`. -/
theorem acceptProb_le_one (A : RandAlg) (x : List Bool) : A.acceptProb x ≤ 1 := by
  unfold acceptProb
  rw [div_le_one (by positivity)]
  have h := Finset.card_le_univ (univ.filter fun ρ : Fin (A.coins.eval x.length) → Bool =>
      A.run x (List.ofFn ρ) = true)
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at h
  exact_mod_cast h

/-- The algorithm that ignores its input and coins and outputs `c`. -/
noncomputable def const (c : Bool) : RandAlg := ⟨fun _ _ => c, 0⟩

/-- The algorithm that ignores its input and coins and outputs `c` is polynomial-time
(non-vacuity of `RandAlg.IsPolyTime`). -/
theorem isPolyTime_const (c : Bool) : (const c).IsPolyTime :=
  polyTimeComputable_const _ c

end RandAlg

/-! ### The two graph distributions -/

/-- The graph on `Fin n` read off from `w : Fin n → Fin n → Bool`: for `i < j` the edge
`{i, j}` is present iff `w i j`. Only the entries above the diagonal are used. -/
def sampleAdj {n : ℕ} (w : Fin n → Fin n → Bool) (i j : Fin n) : Bool :=
  (decide (i < j) && w i j) || (decide (j < i) && w j i)

/-- The graph `sampleAdj w` with a clique planted on `S`. -/
def plantedAdj {n : ℕ} (w : Fin n → Fin n → Bool) (S : Finset (Fin n)) (i j : Fin n) : Bool :=
  sampleAdj w i j || (decide (i ≠ j) && (decide (i ∈ S) && decide (j ∈ S)))

/-- The adjacency matrix as a string of `n * n` bits, row by row. -/
def encAdj {n : ℕ} (a : Fin n → Fin n → Bool) : List Bool :=
  (List.ofFn fun i => List.ofFn (a i)).flatten

/-- The probability that `A` outputs `1` on the adjacency matrix of `G(n, 1/2)`. -/
noncomputable def probNull (A : RandAlg) (n : ℕ) : ℝ :=
  (∑ w : Fin n → Fin n → Bool, A.acceptProb (encAdj (sampleAdj w))) /
    Fintype.card (Fin n → Fin n → Bool)

/-- The probability that `A` outputs `1` on the adjacency matrix of `G(n, 1/2)` with a clique
planted on a uniformly random `k`-subset of the vertices (`0` if `k > n`). -/
noncomputable def probPlanted (A : RandAlg) (n k : ℕ) : ℝ :=
  (∑ w : Fin n → Fin n → Bool, ∑ S ∈ powersetCard k (univ : Finset (Fin n)),
      A.acceptProb (encAdj (plantedAdj w S))) /
    (Fintype.card (Fin n → Fin n → Bool) * n.choose k)

/-- The distinguishing advantage of `A` between the planted and the null distribution. -/
noncomputable def advantage (A : RandAlg) (n k : ℕ) : ℝ :=
  |probPlanted A n k - probNull A n|

/-- The sampled graph is undirected. -/
theorem sampleAdj_symm {n : ℕ} (w : Fin n → Fin n → Bool) (i j : Fin n) :
    sampleAdj w i j = sampleAdj w j i := by
  simp [sampleAdj, Bool.or_comm]

/-- The sampled graph has no loops. -/
theorem sampleAdj_self {n : ℕ} (w : Fin n → Fin n → Bool) (i : Fin n) :
    sampleAdj w i i = false := by
  simp [sampleAdj]

/-- The graph with a planted clique is undirected. -/
theorem plantedAdj_symm {n : ℕ} (w : Fin n → Fin n → Bool) (S : Finset (Fin n)) (i j : Fin n) :
    plantedAdj w S i j = plantedAdj w S j i := by
  simp only [plantedAdj, sampleAdj_symm w i j, ne_comm (a := i), Bool.and_comm (decide (i ∈ S))]

/-- The planted set is a clique of the planted graph. -/
theorem plantedAdj_of_mem {n : ℕ} (w : Fin n → Fin n → Bool) {S : Finset (Fin n)} {i j : Fin n}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) : plantedAdj w S i j = true := by
  simp [plantedAdj, hi, hj, hij]

/-- Planting a clique on at most one vertex does not change the graph. -/
theorem plantedAdj_of_card_le_one {n : ℕ} (w : Fin n → Fin n → Bool) {S : Finset (Fin n)}
    (hS : S.card ≤ 1) : plantedAdj w S = sampleAdj w := by
  funext i j
  have : ¬ (i ≠ j ∧ i ∈ S ∧ j ∈ S) := fun ⟨hij, hi, hj⟩ =>
    hij (Finset.card_le_one.1 hS i hi j hj)
  by_cases hij : i = j
  · simp [plantedAdj, hij]
  · by_cases hi : i ∈ S
    · have hj : j ∉ S := fun hj => this ⟨hij, hi, hj⟩
      simp [plantedAdj, hj]
    · simp [plantedAdj, hi]

/-- For `k ≤ 1` the planted and the null distribution coincide, so no algorithm has any
advantage. -/
theorem advantage_eq_zero_of_le_one (A : RandAlg) (n k : ℕ) (hk : k ≤ 1) (hkn : k ≤ n) :
    advantage A n k = 0 := by
  unfold advantage probPlanted probNull
  have h1 : ∀ w : Fin n → Fin n → Bool, ∑ S ∈ powersetCard k (univ : Finset (Fin n)),
      A.acceptProb (encAdj (plantedAdj w S)) = n.choose k * A.acceptProb (encAdj (sampleAdj w)) := by
    intro w
    rw [Finset.sum_congr rfl fun S hS => by
      rw [plantedAdj_of_card_le_one w (by rw [(Finset.mem_powersetCard.1 hS).2]; exact hk)]]
    simp [Finset.card_powersetCard]
  simp only [h1, ← Finset.mul_sum]
  have hc : (n.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkn).ne'
  have hc' : (Fintype.card (Fin n → Fin n → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [abs_eq_zero, sub_eq_zero]
  field_simp

end Applied.Complexity
