import Applied.Complexity.PlantedClique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.List.OfFn

/-!
# The edge-count test for planted clique

The easy regime of the planted clique problem: when the planted clique has size `k ≫ √n`, the
total number of edges already distinguishes `G(n, 1/2)` from `G(n, 1/2)` with a planted
`k`-clique. Write `N = n (n-1)/2` (vertex pairs) and `K = k (k-1)/2` (pairs inside the planted
set). Under the null the edge count is `Bin(N, 1/2)`, with mean `N/2`; with a planted clique on
a fixed `k`-set it is `K + Bin(N - K, 1/2)`, with mean `N/2 + K/2`.

* `card_signedSum_ge_le`: a Chernoff–Hoeffding bound for sums of independent `±u` signs
  (`u² ≤ 1/4`), proved by counting: at most a fraction `exp (-2 t² / N)` of the sign patterns
  have sum `≥ t`, if at most `N` signs are summed.
* `edgeCountAlg τ`: the deterministic algorithm that reads its input as an adjacency matrix
  and accepts iff the number of edges is at least `τ n`.
* `probNull_edgeCountAlg_le`, `one_sub_le_probPlanted_edgeCountAlg`,
  `advantage_edgeCountAlg_ge`: for `N/2 ≤ τ n ≤ N/2 + K/2` and `k ≤ n`, the false-alarm
  probability is at most `exp (-2 (τ n - N/2)² / N)`, the miss probability at most
  `exp (-2 (N/2 + K/2 - τ n)² / N)`, and the advantage at least `1` minus their sum.
* `advantage_edgeCountAlg_mid_ge`, `advantage_edgeCountAlg_mid_ge'`: at the midpoint threshold
  `N/2 + K/4` the advantage is at least `1 - 2 exp (-K² / (8 N))`, hence at least
  `1 - 2 exp (-k⁴ / (64 n²))` for `2 ≤ k ≤ n`.
* `tendsto_advantage_edgeCountAlg_mid`: if `k n ≤ n` eventually and `k n² / n → ∞`, the
  advantage tends to `1`.

The threshold `midThreshold k` depends on the sequence `k`, and the algorithm is not shown to
run in polynomial time (`RandAlg.IsPolyTime` is not proved for it).
-/

open Finset Real

namespace Applied.Complexity

/-! ### A Chernoff bound by counting -/

/-- The signed sum `∑_{p i j} (±u)` over the pairs satisfying `p`, with `+u` where `w i j` holds
and `-u` where it fails. -/
noncomputable def signedSum {n : ℕ} (p : Fin n → Fin n → Prop) [DecidableRel p] (u : ℝ)
    (w : Fin n → Fin n → Bool) : ℝ :=
  ∑ i, ∑ j, if p i j then (if w i j then u else -u) else 0

/-- The number of pairs satisfying `p`. -/
def pairsCard {n : ℕ} (p : Fin n → Fin n → Prop) [DecidableRel p] : ℕ :=
  (univ.filter fun q : Fin n × Fin n => p q.1 q.2).card

lemma sum_ite_pairs {n : ℕ} (p : Fin n → Fin n → Prop) [DecidableRel p] (c : ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, (if p i j then c else 0) = c * pairsCard p := by
  rw [← Fintype.sum_prod_type' (fun i j => if p i j then c else 0), ← Finset.sum_filter,
    sum_const, nsmul_eq_mul, mul_comm]
  rfl

lemma sum_exp_signedSum_le {n : ℕ} (p : Fin n → Fin n → Prop) [DecidableRel p] {u : ℝ}
    (hu : u ^ 2 ≤ 1 / 4) (s : ℝ) :
    ∑ w : Fin n → Fin n → Bool, exp (s * signedSum p u w)
      ≤ 2 ^ (n * n) * exp (s ^ 2 * pairsCard p / 8) := by
  classical
  set g : Fin n → Fin n → Bool → ℝ := fun i j b =>
    exp (s * if p i j then (if b then u else -u) else 0) with hg
  have h1 : ∀ w : Fin n → Fin n → Bool, exp (s * signedSum p u w) = ∏ i, ∏ j, g i j (w i j) := by
    intro w
    rw [signedSum, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (r : Fin n → Bool) => ∏ j, g i j (r j))]
  rw [Finset.prod_congr rfl fun i _ => (Fintype.prod_sum (fun j (b : Bool) => g i j b)).symm]
  have h2 : ∀ i j, ∑ b : Bool, g i j b ≤ 2 * exp (if p i j then s ^ 2 / 8 else 0) := by
    intro i j
    by_cases hp : p i j
    · simp only [hg, hp, ite_true, Fintype.sum_bool, Bool.false_eq_true, ite_false]
      have hc : exp (s * u) + exp (s * -u) = 2 * cosh (s * u) := by
        rw [Real.cosh_eq]; ring_nf
      rw [hc]
      have h3 := Real.cosh_le_exp_half_sq (s * u)
      have h4 : exp ((s * u) ^ 2 / 2) ≤ exp (s ^ 2 / 8) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ s ^ 2 := sq_nonneg s
        nlinarith
      linarith
    · simp [hg, hp]
  calc ∏ i, ∏ j, ∑ b : Bool, g i j b
      ≤ ∏ i : Fin n, ∏ j : Fin n, 2 * exp (if p i j then s ^ 2 / 8 else 0) := by
        apply Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ =>
          Finset.sum_nonneg fun b _ => (Real.exp_pos _).le)
        intro i _
        exact Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun b _ => (Real.exp_pos _).le)
          (fun j _ => h2 i j)
    _ = 2 ^ (n * n) * exp (s ^ 2 * pairsCard p / 8) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← Real.exp_sum, sum_ite_pairs]
        rw [← pow_mul]
        congr 2
        ring

/-- **Chernoff bound, counting form.** For `u² ≤ 1/4`, `t ≥ 0` and `pairsCard p ≤ N`, at most a
fraction `exp (-2 t² / N)` of all `w` have `signedSum p u w ≥ t`. -/
lemma card_signedSum_ge_le {n : ℕ} (p : Fin n → Fin n → Prop) [DecidableRel p] {u : ℝ}
    (hu : u ^ 2 ≤ 1 / 4) {t N : ℝ} (ht : 0 ≤ t) (hN : (pairsCard p : ℝ) ≤ N) :
    ((univ.filter fun w : Fin n → Fin n → Bool => t ≤ signedSum p u w).card : ℝ)
      ≤ 2 ^ (n * n) * exp (-2 * t ^ 2 / N) := by
  set s := 4 * t / N with hs
  have hs0 : 0 ≤ s := by
    rcases (le_or_gt N 0) with h | h
    · have : N = 0 := le_antisymm h (le_trans (Nat.cast_nonneg _) hN)
      simp [hs, this]
    · positivity
  have hmarkov : ((univ.filter fun w : Fin n → Fin n → Bool => t ≤ signedSum p u w).card : ℝ)
      * exp (s * t) ≤ ∑ w : Fin n → Fin n → Bool, exp (s * signedSum p u w) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    calc ∑ w ∈ univ.filter fun w : Fin n → Fin n → Bool => t ≤ signedSum p u w, exp (s * t)
        ≤ ∑ w ∈ univ.filter fun w : Fin n → Fin n → Bool => t ≤ signedSum p u w,
            exp (s * signedSum p u w) := by
          apply Finset.sum_le_sum
          intro w hw
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mem_filter.mp hw).2 hs0)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => (Real.exp_pos _).le)
  have h := hmarkov.trans (sum_exp_signedSum_le p hu s)
  have hexp : exp (s ^ 2 * pairsCard p / 8) ≤ exp (-2 * t ^ 2 / N) * exp (s * t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rcases (le_or_gt N 0) with hN0 | hN0
    · have : N = 0 := le_antisymm hN0 (le_trans (Nat.cast_nonneg _) hN)
      simp [hs, this]
    · rw [hs]
      have hm : (pairsCard p : ℝ) / N ^ 2 ≤ 1 / N := by
        rw [div_le_div_iff₀ (by positivity) hN0]; nlinarith
      have e1 : (4 * t / N) ^ 2 * pairsCard p / 8 = 2 * t ^ 2 * ((pairsCard p : ℝ) / N ^ 2) := by
        field_simp; ring
      have e2 : -2 * t ^ 2 / N + 4 * t / N * t = 2 * t ^ 2 * (1 / N) := by
        field_simp; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hm (by positivity)
  have hpos : 0 < exp (s * t) := Real.exp_pos _
  have := h.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  rw [← mul_assoc] at this
  exact le_of_mul_le_mul_right this hpos

lemma signedSum_neg {n : ℕ} (p : Fin n → Fin n → Prop) [DecidableRel p] (u : ℝ)
    (w : Fin n → Fin n → Bool) : signedSum p (-u) w = - signedSum p u w := by
  simp only [signedSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-! ### Edge counts -/

/-- The number of pairs `(i, j)` satisfying `p` with `w i j` true. -/
def pairsTrue {n : ℕ} (p : Fin n → Fin n → Prop) [DecidableRel p] (w : Fin n → Fin n → Bool) :
    ℕ :=
  (univ.filter fun q : Fin n × Fin n => p q.1 q.2 ∧ w q.1 q.2 = true).card

lemma cast_pairsTrue {n : ℕ} (p : Fin n → Fin n → Prop) [DecidableRel p]
    (w : Fin n → Fin n → Bool) :
    (pairsTrue p w : ℝ) = pairsCard p / 2 + signedSum p (1 / 2) w := by
  have h1 : (pairsTrue p w : ℝ) = ∑ i, ∑ j, if p i j ∧ w i j = true then (1 : ℝ) else 0 := by
    rw [pairsTrue, Finset.natCast_card_filter]
    exact Fintype.sum_prod_type' (fun i j => if p i j ∧ w i j = true then (1 : ℝ) else 0)
  have h2 : (pairsCard p : ℝ) / 2 = ∑ i, ∑ j, if p i j then (1 / 2 : ℝ) else 0 := by
    rw [sum_ite_pairs]; ring
  rw [h1, h2, signedSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hp : p i j <;> cases w i j <;> simp [hp]; norm_num

/-- The number of edges `{i, j}`, `i < j`, of the graph with adjacency matrix `a`; only the
entries above the diagonal are read. -/
def edgeCount {n : ℕ} (a : Fin n → Fin n → Bool) : ℕ :=
  (univ.filter fun q : Fin n × Fin n => q.1 < q.2 ∧ a q.1 q.2 = true).card

/-- `2 · #{(i, j) : i < j, i, j ∈ T} = |T| (|T| - 1)`. -/
lemma two_mul_pairsCard_in {n : ℕ} (T : Finset (Fin n)) :
    2 * pairsCard (fun i j : Fin n => i < j ∧ i ∈ T ∧ j ∈ T) = T.card * (T.card - 1) := by
  set A := univ.filter fun q : Fin n × Fin n => q.1 < q.2 ∧ q.1 ∈ T ∧ q.2 ∈ T with hA
  have hoff : T.offDiag = A ∪ A.image Prod.swap := by
    ext ⟨i, j⟩
    simp only [mem_offDiag, hA, mem_union, mem_filter, mem_univ, true_and, mem_image,
      Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨hi, hj, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨h, hi, hj⟩
      · exact Or.inr ⟨j, i, ⟨h, hj, hi⟩, rfl, rfl⟩
    · rintro (⟨h, hi, hj⟩ | ⟨a, b, ⟨h, ha, hb⟩, rfl, rfl⟩)
      · exact ⟨hi, hj, h.ne⟩
      · exact ⟨hb, ha, h.ne'⟩
  have hdisj : Disjoint A (A.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hq'
    simp only [hA, mem_filter] at hq hr
    exact absurd hq.2.1 (not_lt.mpr hr.2.1.le)
  have hc := Finset.offDiag_card T
  rw [hoff, card_union_of_disjoint hdisj,
    card_image_of_injective _ Prod.swap_injective] at hc
  change 2 * A.card = _
  rw [Nat.mul_sub_one, ← hc]; ring

lemma cast_nat_mul_pred (m : ℕ) : ((m * (m - 1) : ℕ) : ℝ) = m * (m - 1) := by
  cases m with
  | zero => simp
  | succ m => push_cast; simp

/-- The number of pairs `i < j` in `Fin n` is `n (n - 1) / 2`. -/
lemma pairsCard_lt (n : ℕ) : (pairsCard (fun i j : Fin n => i < j) : ℝ) = n * (n - 1) / 2 := by
  have h := two_mul_pairsCard_in (univ : Finset (Fin n))
  have he : pairsCard (fun i j : Fin n => i < j ∧ i ∈ univ ∧ j ∈ univ)
      = pairsCard (fun i j : Fin n => i < j) := by
    unfold pairsCard; congr 1; ext q; simp
  rw [he, card_univ, Fintype.card_fin] at h
  have h' : ((2 * pairsCard (fun i j : Fin n => i < j) : ℕ) : ℝ) = n * (n - 1) := by
    rw [h, cast_nat_mul_pred]
  push_cast at h'; linarith

lemma pairsCard_in {n : ℕ} (S : Finset (Fin n)) :
    (pairsCard (fun i j : Fin n => i < j ∧ i ∈ S ∧ j ∈ S) : ℝ) = S.card * (S.card - 1) / 2 := by
  have h' : ((2 * pairsCard (fun i j : Fin n => i < j ∧ i ∈ S ∧ j ∈ S) : ℕ) : ℝ)
      = S.card * (S.card - 1) := by
    rw [two_mul_pairsCard_in, cast_nat_mul_pred]
  push_cast at h'; linarith

lemma edgeCount_sampleAdj {n : ℕ} (w : Fin n → Fin n → Bool) :
    edgeCount (sampleAdj w) = pairsTrue (fun i j : Fin n => i < j) w := by
  unfold edgeCount pairsTrue
  congr 1
  refine Finset.filter_congr fun q _ => ?_
  constructor
  · rintro ⟨h, h'⟩; refine ⟨h, ?_⟩
    simpa [sampleAdj, h, not_lt_of_gt h] using h'
  · rintro ⟨h, h'⟩; refine ⟨h, ?_⟩
    simp [sampleAdj, h, h']

/-- The pairs `i < j` not both in `S`. -/
abbrev outside {n : ℕ} (S : Finset (Fin n)) (i j : Fin n) : Prop := i < j ∧ ¬ (i ∈ S ∧ j ∈ S)

lemma edgeCount_plantedAdj {n : ℕ} (w : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    edgeCount (plantedAdj w S) = pairsCard (fun i j : Fin n => i < j ∧ i ∈ S ∧ j ∈ S)
      + pairsTrue (outside S) w := by
  unfold edgeCount pairsTrue pairsCard
  rw [← card_union_of_disjoint]
  · congr 1
    ext ⟨i, j⟩
    simp only [mem_filter, mem_univ, true_and, mem_union]
    by_cases h : i < j
    · have hne : i ≠ j := h.ne
      by_cases hS : i ∈ S ∧ j ∈ S
      · simp [plantedAdj, sampleAdj, h, hne, hS.1, hS.2]
      · have : ¬ (i ∈ S ∧ j ∈ S) := hS
        simp only [plantedAdj, sampleAdj, h, not_lt_of_gt h]
        by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp_all [outside]
    · simp [h]
  · rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [mem_filter] at hq hq'
    exact hq'.2.1.2 hq.2.2

lemma pairsCard_outside {n : ℕ} (S : Finset (Fin n)) :
    pairsCard (fun i j : Fin n => i < j ∧ i ∈ S ∧ j ∈ S) + pairsCard (outside S)
      = pairsCard (fun i j : Fin n => i < j) := by
  unfold pairsCard
  have := Finset.card_filter_add_card_filter_not (s := univ.filter fun q : Fin n × Fin n => q.1 < q.2)
    (fun q : Fin n × Fin n => q.1 ∈ S ∧ q.2 ∈ S)
  simp only [filter_filter] at this
  rw [← this]

/-! ### Error bounds for the edge-count test -/

/-- Under `G(n, 1/2)`: at most a fraction `exp (-2 (τ - N/2)² / N)` of the samples `w` give a
graph with at least `τ` edges, for `τ ≥ N/2`, where `N = n (n-1)/2`. -/
theorem card_null_edgeCount_ge_le (n : ℕ) {τ : ℝ} (hτ : (n * (n - 1) / 2 : ℝ) / 2 ≤ τ) :
    ((univ.filter fun w : Fin n → Fin n → Bool => τ ≤ edgeCount (sampleAdj w)).card : ℝ)
      ≤ 2 ^ (n * n) * exp (-2 * (τ - (n * (n - 1) / 2 : ℝ) / 2) ^ 2 / (n * (n - 1) / 2)) := by
  have hsub : (univ.filter fun w : Fin n → Fin n → Bool => τ ≤ edgeCount (sampleAdj w))
      ⊆ univ.filter fun w => τ - (n * (n - 1) / 2 : ℝ) / 2
          ≤ signedSum (fun i j : Fin n => i < j) (1 / 2) w := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    rw [edgeCount_sampleAdj, cast_pairsTrue, pairsCard_lt] at hw
    linarith
  refine (Nat.cast_le.mpr (card_le_card hsub)).trans ?_
  exact card_signedSum_ge_le _ (by norm_num) (by linarith) (pairsCard_lt n).le

/-- With a planted clique on a `k`-set `S`: at most a fraction
`exp (-2 (N/2 + K/2 - τ)² / N)` of the samples `w` give a graph with fewer than `τ` edges, for
`τ ≤ N/2 + K/2`, where `N = n (n-1)/2` and `K = k (k-1)/2`. -/
theorem card_planted_edgeCount_lt_le {n : ℕ} (S : Finset (Fin n)) {τ : ℝ}
    (hτ : τ ≤ (n * (n - 1) / 2 : ℝ) / 2 + (S.card * (S.card - 1) / 2 : ℝ) / 2) :
    ((univ.filter fun w : Fin n → Fin n → Bool => ¬ τ ≤ edgeCount (plantedAdj w S)).card : ℝ)
      ≤ 2 ^ (n * n) * exp (-2 * ((n * (n - 1) / 2 : ℝ) / 2
          + (S.card * (S.card - 1) / 2 : ℝ) / 2 - τ) ^ 2 / (n * (n - 1) / 2)) := by
  have hout := pairsCard_outside S
  have hout' : (pairsCard (outside S) : ℝ)
      = n * (n - 1) / 2 - S.card * (S.card - 1) / 2 := by
    rw [← pairsCard_lt, ← pairsCard_in, ← hout]; push_cast; ring
  have hsub : (univ.filter fun w : Fin n → Fin n → Bool => ¬ τ ≤ edgeCount (plantedAdj w S))
      ⊆ univ.filter fun w => (n * (n - 1) / 2 : ℝ) / 2 + (S.card * (S.card - 1) / 2 : ℝ) / 2 - τ
          ≤ signedSum (outside S) (-(1 / 2)) w := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and, not_le] at hw ⊢
    rw [edgeCount_plantedAdj] at hw
    push_cast at hw
    rw [cast_pairsTrue, pairsCard_in, hout'] at hw
    rw [signedSum_neg]
    linarith
  refine (Nat.cast_le.mpr (card_le_card hsub)).trans ?_
  refine card_signedSum_ge_le _ (by norm_num) (by linarith) ?_
  rw [← pairsCard_lt, ← hout]; push_cast
  linarith [(Nat.cast_nonneg (pairsCard fun i j : Fin n => i < j ∧ i ∈ S ∧ j ∈ S) : (0 : ℝ) ≤ _)]

/-! ### The edge-count test as a randomized algorithm on encoded adjacency matrices -/

lemma idx_div {n : ℕ} (i j : Fin n) : (i * n + j : ℕ) / n = i := by
  have hn : 0 < n := Fin.pos i
  rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt j.2, Nat.add_zero]

lemma idx_mod {n : ℕ} (i j : Fin n) : (i * n + j : ℕ) % n = j := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]

lemma idx_lt {n : ℕ} (i j : Fin n) : (i * n + j : ℕ) < n * n :=
  calc (i * n + j : ℕ) < (i + 1) * n := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ n * n := Nat.mul_le_mul_right _ i.2

lemma encAdj_eq_ofFn {n : ℕ} (a : Fin n → Fin n → Bool) :
    encAdj a = List.ofFn (fun p : Fin (n * n) =>
      a ⟨p / n, Nat.div_lt_of_lt_mul p.2⟩
        ⟨p % n, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp [h] at p; exact p.elim0)⟩) := by
  rw [List.ofFn_mul]
  unfold encAdj
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => List.ofFn_inj.mpr (funext fun j => ?_))
  congr 1
  · exact Fin.ext (idx_div i j).symm
  · exact Fin.ext (idx_mod i j).symm

lemma encAdj_length {n : ℕ} (a : Fin n → Fin n → Bool) : (encAdj a).length = n * n := by
  rw [encAdj_eq_ofFn, List.length_ofFn]

lemma encAdj_getD {n : ℕ} (a : Fin n → Fin n → Bool) (i j : Fin n) :
    (encAdj a).getD (i * n + j) false = a i j := by
  rw [encAdj_eq_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [idx_lt i j, ↓reduceDIte, Option.getD_some]
  congr 1
  · exact Fin.ext (idx_div i j)
  · exact Fin.ext (idx_mod i j)

/-- The edge count read off a bit string `x` taken as an `m × m` adjacency matrix, row by row
(entries beyond the end of `x` count as `false`). -/
def rawEdgeCount (x : List Bool) (m : ℕ) : ℕ :=
  (univ.filter fun q : Fin m × Fin m => q.1 < q.2 ∧ x.getD (q.1 * m + q.2) false = true).card

lemma rawEdgeCount_encAdj {n : ℕ} (a : Fin n → Fin n → Bool) :
    rawEdgeCount (encAdj a) n = edgeCount a := by
  unfold rawEdgeCount edgeCount
  simp_rw [encAdj_getD]

/-- **The edge-count test** with threshold `τ n`: on an input of length `L` it sets
`m = ⌊√L⌋`, reads the input as an `m × m` adjacency matrix, and accepts iff the number of
entries `(i, j)`, `i < j`, equal to `1` is at least `τ m`. It uses no coins. -/
noncomputable def edgeCountAlg (τ : ℕ → ℝ) : RandAlg :=
  ⟨fun x _ => decide (τ (Nat.sqrt x.length) ≤ rawEdgeCount x (Nat.sqrt x.length)), 0⟩

lemma acceptProb_edgeCountAlg (τ : ℕ → ℝ) {n : ℕ} (a : Fin n → Fin n → Bool) :
    (edgeCountAlg τ).acceptProb (encAdj a) = if τ n ≤ edgeCount a then 1 else 0 := by
  have hs : Nat.sqrt (encAdj a).length = n := by rw [encAdj_length, Nat.sqrt_eq]
  unfold RandAlg.acceptProb edgeCountAlg
  simp only [Polynomial.eval_zero, pow_zero, div_one, hs, rawEdgeCount_encAdj]
  split_ifs with h <;> simp [h]

lemma probNull_edgeCountAlg (τ : ℕ → ℝ) (n : ℕ) :
    probNull (edgeCountAlg τ) n
      = ((univ.filter fun w : Fin n → Fin n → Bool => τ n ≤ edgeCount (sampleAdj w)).card : ℝ)
        / 2 ^ (n * n) := by
  unfold probNull
  simp_rw [acceptProb_edgeCountAlg]
  rw [Finset.sum_boole]
  simp [Fintype.card_pi, pow_mul]

lemma probPlanted_edgeCountAlg (τ : ℕ → ℝ) (n k : ℕ) :
    probPlanted (edgeCountAlg τ) n k
      = (∑ S ∈ powersetCard k (univ : Finset (Fin n)),
          ((univ.filter fun w : Fin n → Fin n → Bool =>
            τ n ≤ edgeCount (plantedAdj w S)).card : ℝ)) / (2 ^ (n * n) * n.choose k) := by
  unfold probPlanted
  simp_rw [acceptProb_edgeCountAlg]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_boole]
  simp [Fintype.card_pi, pow_mul]

/-! ### Main bounds -/

/-- **False-alarm probability of the edge-count test.** Under `G(n, 1/2)` the test with
threshold `τ n ≥ N/2` accepts with probability at most `exp (-2 (τ n - N/2)² / N)`, where
`N = n (n-1)/2` is the number of vertex pairs. -/
theorem probNull_edgeCountAlg_le (τ : ℕ → ℝ) (n : ℕ)
    (hτ : (n * (n - 1) / 2 : ℝ) / 2 ≤ τ n) :
    probNull (edgeCountAlg τ) n
      ≤ exp (-2 * (τ n - (n * (n - 1) / 2 : ℝ) / 2) ^ 2 / (n * (n - 1) / 2)) := by
  rw [probNull_edgeCountAlg, div_le_iff₀ (by positivity), mul_comm]
  exact card_null_edgeCount_ge_le n hτ

/-- **Miss probability of the edge-count test.** With a clique planted on a uniformly random
`k`-subset, `k ≤ n`, the test with threshold `τ n ≤ N/2 + K/2` accepts with probability at
least `1 - exp (-2 (N/2 + K/2 - τ n)² / N)`, where `N = n (n-1)/2` and `K = k (k-1)/2`. -/
theorem one_sub_le_probPlanted_edgeCountAlg (τ : ℕ → ℝ) {n k : ℕ} (hkn : k ≤ n)
    (hτ : τ n ≤ (n * (n - 1) / 2 : ℝ) / 2 + (k * (k - 1) / 2 : ℝ) / 2) :
    1 - exp (-2 * ((n * (n - 1) / 2 : ℝ) / 2 + (k * (k - 1) / 2 : ℝ) / 2 - τ n) ^ 2
        / (n * (n - 1) / 2))
      ≤ probPlanted (edgeCountAlg τ) n k := by
  set e := exp (-2 * ((n * (n - 1) / 2 : ℝ) / 2 + (k * (k - 1) / 2 : ℝ) / 2 - τ n) ^ 2
        / (n * (n - 1) / 2)) with he
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hS : ∀ S ∈ powersetCard k (univ : Finset (Fin n)),
      (2 : ℝ) ^ (n * n) * (1 - e) ≤ ((univ.filter fun w : Fin n → Fin n → Bool =>
            τ n ≤ edgeCount (plantedAdj w S)).card : ℝ) := by
    intro S hS
    have hcard : S.card = k := (mem_powersetCard.mp hS).2
    have hb := card_planted_edgeCount_lt_le S (τ := τ n) (by rw [hcard]; exact hτ)
    rw [hcard, ← he] at hb
    have hsum := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n → Fin n → Bool)))
      (fun w => τ n ≤ edgeCount (plantedAdj w S))
    have hsum' : ((univ.filter fun w : Fin n → Fin n → Bool =>
            τ n ≤ edgeCount (plantedAdj w S)).card : ℝ)
        + ((univ.filter fun w : Fin n → Fin n → Bool =>
            ¬ τ n ≤ edgeCount (plantedAdj w S)).card : ℝ) = 2 ^ (n * n) := by
      rw [← Nat.cast_add, hsum]; simp [Fintype.card_pi, pow_mul]
    linarith
  rw [probPlanted_edgeCountAlg, le_div_iff₀ (by positivity)]
  have := Finset.sum_le_sum hS
  rw [Finset.sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

/-- **The edge-count test distinguishes.** For `k ≤ n` and a threshold
`N/2 ≤ τ n ≤ N/2 + K/2` (`N = n (n-1)/2`, `K = k (k-1)/2`), the advantage of the edge-count
test is at least `1 - exp (-2 (τ n - N/2)² / N) - exp (-2 (N/2 + K/2 - τ n)² / N)`. -/
theorem advantage_edgeCountAlg_ge (τ : ℕ → ℝ) {n k : ℕ} (hkn : k ≤ n)
    (hτ₁ : (n * (n - 1) / 2 : ℝ) / 2 ≤ τ n)
    (hτ₂ : τ n ≤ (n * (n - 1) / 2 : ℝ) / 2 + (k * (k - 1) / 2 : ℝ) / 2) :
    1 - exp (-2 * (τ n - (n * (n - 1) / 2 : ℝ) / 2) ^ 2 / (n * (n - 1) / 2))
      - exp (-2 * ((n * (n - 1) / 2 : ℝ) / 2 + (k * (k - 1) / 2 : ℝ) / 2 - τ n) ^ 2
        / (n * (n - 1) / 2))
      ≤ advantage (edgeCountAlg τ) n k := by
  have h1 := probNull_edgeCountAlg_le τ n hτ₁
  have h2 := one_sub_le_probPlanted_edgeCountAlg τ hkn hτ₂
  unfold advantage
  linarith [le_abs_self (probPlanted (edgeCountAlg τ) n k - probNull (edgeCountAlg τ) n)]

/-- The threshold `N/2 + K/4` halfway between the two means, for a planted-clique size
sequence `k`. -/
noncomputable def midThreshold (k : ℕ → ℕ) (n : ℕ) : ℝ :=
  (n * (n - 1) / 2 : ℝ) / 2 + (k n * (k n - 1) / 2 : ℝ) / 4

lemma nat_mul_pred_nonneg (m : ℕ) : (0 : ℝ) ≤ m * (m - 1) := by
  rw [← cast_nat_mul_pred]; exact Nat.cast_nonneg _

/-- **Edge-count test at the midpoint threshold.** For `k n ≤ n`, the edge-count test with
threshold `N/2 + K/4` has advantage at least `1 - 2 exp (-K² / (8 N))`, where `N = n (n-1)/2`
and `K = k (k-1)/2`. -/
theorem advantage_edgeCountAlg_mid_ge (k : ℕ → ℕ) {n : ℕ} (hkn : k n ≤ n) :
    1 - 2 * exp (-((k n * (k n - 1) / 2 : ℝ) ^ 2) / (8 * (n * (n - 1) / 2)))
      ≤ advantage (edgeCountAlg (midThreshold k)) n (k n) := by
  have hK := nat_mul_pred_nonneg (k n)
  have h := advantage_edgeCountAlg_ge (midThreshold k) hkn
    (by unfold midThreshold; linarith) (by unfold midThreshold; linarith)
  have e1 : -2 * (midThreshold k n - (n * (n - 1) / 2 : ℝ) / 2) ^ 2 / (n * (n - 1) / 2)
      = -((k n * (k n - 1) / 2 : ℝ) ^ 2) / (8 * (n * (n - 1) / 2)) := by
    unfold midThreshold
    generalize (n * (n - 1) / 2 : ℝ) = N
    generalize (k n * (k n - 1) / 2 : ℝ) = K
    ring
  have e2 : -2 * ((n * (n - 1) / 2 : ℝ) / 2 + (k n * (k n - 1) / 2 : ℝ) / 2 - midThreshold k n) ^ 2
        / (n * (n - 1) / 2)
      = -((k n * (k n - 1) / 2 : ℝ) ^ 2) / (8 * (n * (n - 1) / 2)) := by
    unfold midThreshold
    generalize (n * (n - 1) / 2 : ℝ) = N
    generalize (k n * (k n - 1) / 2 : ℝ) = K
    ring
  rw [e1, e2] at h
  linarith

/-- For `2 ≤ k ≤ n` the midpoint edge-count test has advantage at least
`1 - 2 exp (-k⁴ / (64 n²))`. -/
theorem advantage_edgeCountAlg_mid_ge' (k : ℕ → ℕ) {n : ℕ} (hk : 2 ≤ k n) (hkn : k n ≤ n) :
    1 - 2 * exp (-((k n : ℝ) ^ 4 / (64 * (n : ℝ) ^ 2)))
      ≤ advantage (edgeCountAlg (midThreshold k)) n (k n) := by
  refine le_trans ?_ (advantage_edgeCountAlg_mid_ge k hkn)
  have hk' : (2 : ℝ) ≤ k n := by exact_mod_cast hk
  have hn' : (k n : ℝ) ≤ n := by exact_mod_cast hkn
  have hN : (0 : ℝ) < n * (n - 1) / 2 := by
    have : (2 : ℝ) ≤ n := hk'.trans hn'
    have : (0 : ℝ) < n * (n - 1) := by nlinarith
    linarith
  have hNle : (n * (n - 1) / 2 : ℝ) ≤ n ^ 2 / 2 := by nlinarith
  have hK : (k n : ℝ) ^ 2 / 4 ≤ k n * (k n - 1) / 2 := by nlinarith
  have hK0 : (0 : ℝ) ≤ (k n : ℝ) ^ 2 / 4 := by positivity
  have key : (k n : ℝ) ^ 4 / (64 * (n : ℝ) ^ 2)
      ≤ (k n * (k n - 1) / 2 : ℝ) ^ 2 / (8 * (n * (n - 1) / 2)) := by
    have hn0 : (0 : ℝ) < n := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((k n : ℝ) ^ 2 / 4) ^ 2 ≤ (k n * (k n - 1) / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hK0 hK 2
    have h2 : (0 : ℝ) ≤ (k n : ℝ) ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hNle h2, mul_le_mul_of_nonneg_left h1
      (by positivity : (0 : ℝ) ≤ 64 * (n : ℝ) ^ 2)]
  have : exp (-((k n * (k n - 1) / 2 : ℝ) ^ 2) / (8 * (n * (n - 1) / 2)))
      ≤ exp (-((k n : ℝ) ^ 4 / (64 * (n : ℝ) ^ 2))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]; linarith
  linarith

lemma probNull_nonneg (A : RandAlg) (n : ℕ) : 0 ≤ probNull A n :=
  div_nonneg (Finset.sum_nonneg fun _ _ => A.acceptProb_nonneg _) (Nat.cast_nonneg _)

lemma probNull_le_one (A : RandAlg) (n : ℕ) : probNull A n ≤ 1 := by
  unfold probNull
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  calc ∑ w : Fin n → Fin n → Bool, A.acceptProb (encAdj (sampleAdj w))
      ≤ ∑ w : Fin n → Fin n → Bool, (1 : ℝ) :=
        Finset.sum_le_sum fun w _ => A.acceptProb_le_one _
    _ = _ := by simp

lemma probPlanted_nonneg (A : RandAlg) (n k : ℕ) : 0 ≤ probPlanted A n k :=
  div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => A.acceptProb_nonneg _)
    (by positivity)

lemma probPlanted_le_one (A : RandAlg) (n k : ℕ) : probPlanted A n k ≤ 1 := by
  unfold probPlanted
  refine div_le_one_of_le₀ ?_ (by positivity)
  calc ∑ w : Fin n → Fin n → Bool, ∑ S ∈ powersetCard k (univ : Finset (Fin n)),
        A.acceptProb (encAdj (plantedAdj w S))
      ≤ ∑ w : Fin n → Fin n → Bool, ∑ S ∈ powersetCard k (univ : Finset (Fin n)), (1 : ℝ) :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun S _ => A.acceptProb_le_one _
    _ = _ := by simp

lemma advantage_le_one (A : RandAlg) (n k : ℕ) : advantage A n k ≤ 1 := by
  unfold advantage
  rw [abs_le]
  constructor <;> linarith [probNull_nonneg A n, probNull_le_one A n, probPlanted_nonneg A n k,
    probPlanted_le_one A n k]

/-- **Above `√n` the planted clique is detectable.** If `k n ≤ n` for all large `n` and
`k n² / n → ∞`, the advantage of the midpoint edge-count test tends to `1`. -/
theorem tendsto_advantage_edgeCountAlg_mid (k : ℕ → ℕ)
    (hkn : ∀ᶠ n in Filter.atTop, k n ≤ n)
    (hk : Filter.Tendsto (fun n => (k n : ℝ) ^ 2 / n) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => advantage (edgeCountAlg (midThreshold k)) n (k n))
      Filter.atTop (nhds 1) := by
  have hsq : Filter.Tendsto (fun n => ((k n : ℝ) ^ 2 / n) ^ 2 / 64) Filter.atTop Filter.atTop := by
    simp_rw [pow_two ((k _ : ℝ) ^ 2 / _)]
    exact (hk.atTop_mul_atTop₀ hk).atTop_div_const (by norm_num)
  have hlow : Filter.Tendsto (fun n => 1 - 2 * exp (-(((k n : ℝ) ^ 2 / n) ^ 2 / 64)))
      Filter.atTop (nhds 1) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq).const_mul 2
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Filter.Eventually.of_forall fun n => advantage_le_one _ _ _)
  filter_upwards [hkn, hk.eventually_ge_atTop 4, Filter.eventually_ge_atTop 1] with n h1 h2 h3
  have hn : (0 : ℝ) < n := by exact_mod_cast h3
  have hk2 : 2 ≤ k n := by
    have : (4 : ℝ) * n ≤ (k n : ℝ) ^ 2 := by rwa [le_div_iff₀ hn] at h2
    have h1' : (1 : ℝ) ≤ n := by exact_mod_cast h3
    have : (4 : ℝ) ≤ (k n : ℝ) ^ 2 := by nlinarith
    have : (2 : ℝ) ≤ k n := by nlinarith [(Nat.cast_nonneg (k n) : (0 : ℝ) ≤ k n)]
    exact_mod_cast this
  have e : ((k n : ℝ) ^ 2 / n) ^ 2 / 64 = (k n : ℝ) ^ 4 / (64 * (n : ℝ) ^ 2) := by
    field_simp
  rw [e]
  exact advantage_edgeCountAlg_mid_ge' k hk2 h1

end Applied.Complexity
