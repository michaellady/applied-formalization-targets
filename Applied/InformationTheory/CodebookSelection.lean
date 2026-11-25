import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Selecting a codebook: greedy choice and expurgation

Pure finite combinatorics, with no channel in sight.  This is the selection step shared by the
achievability proofs for the binary erasure channel (`ErasureAchievability`, `ErasureCapacity`),
the binary symmetric channel (`BscCapacity`) and the deletion channel (`DeletionCoding`).

Setting: `ι` is a finite nonempty type of *candidate words* (`N = Fintype.card ι` of them) and
`f : ι → ι → ℝ` is a nonnegative "confusion weight" (`f x x'` bounds the probability that `x'` is
mistaken for `x`).  Assume every row sum is small: `∑ x', f x x' ≤ B` for all `x`.  A *codebook*
is a family `c : Fin K → ι` (repetitions are allowed).

## Main definitions

* `offSum f c = ∑_{m ≠ m'} f (c m) (c m')`: the total off-diagonal weight of a codebook.

## Main results

* `exists_codebook_offSum_le_of_symm` (**greedy choice, symmetric `f`**): there are `K`
  codewords with `offSum f c ≤ K² · B / N`.
* `exists_codebook_offSum_le` (**greedy choice, general `f`**): there are `K` codewords with
  `offSum f c ≤ 3 K² · B / N`, all of whose column sums are at most `2 B`.
* `exists_subcodebook_rows_le` (**expurgation**): out of any `2 K` codewords one can keep `K`
  such that every remaining codeword has off-diagonal row sum at most `offSum f c / K`, i.e.
  the *maximal* row sum is controlled by the *average* one.
* `exists_codebook_rows_le_of_symm`, `exists_codebook_rows_le'`: the combination, giving `K`
  codewords with every off-diagonal row sum at most `4 K B / N` (symmetric `f`) resp.
  `12 K B / N` (general `f`).

## Not in this file

No probability: turning a row-sum bound into a bound on the maximal error probability of a
block code is done where the decoder is defined (`becCode_errorProb_le_tail_add`,
`exists_deletion_code`, …).  The constants `4` and `12` are not optimised.
-/

open Finset

namespace Applied.InformationTheory

variable {ι : Type*}

/-! ### The off-diagonal sum of a codebook -/

/-- The total off-diagonal sum `∑_{m ≠ m'} f (c m) (c m')` of `f` over a codebook `c`. -/
noncomputable def offSum (f : ι → ι → ℝ) {K : ℕ} (c : Fin K → ι) : ℝ :=
  ∑ m, ∑ m', if m = m' then 0 else f (c m) (c m')

/-- Adding a codeword `x` in front of a codebook `c` increases the off-diagonal sum by the row
sum and the column sum of `x` against `c`. -/
lemma offSum_cons (f : ι → ι → ℝ) {K : ℕ} (x : ι) (c : Fin K → ι) :
    offSum f (Fin.cons x c : Fin (K + 1) → ι) =
      (∑ j, f x (c j)) + (∑ j, f (c j) x) + offSum f c := by
  unfold offSum
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.succ_inj,
    (Fin.succ_ne_zero _).symm, Fin.succ_ne_zero, ite_true, ite_false, zero_add,
    Finset.sum_add_distrib]
  ring

/-- Every off-diagonal row sum of a codebook for a nonnegative `f` is nonnegative. -/
lemma offRow_nonneg {f : ι → ι → ℝ} (hf0 : ∀ x x', 0 ≤ f x x') {K : ℕ} (c : Fin K → ι)
    (m : Fin K) : 0 ≤ ∑ m', if m = m' then 0 else f (c m) (c m') :=
  Finset.sum_nonneg fun m' _ => by split_ifs; exacts [le_rfl, hf0 _ _]

/-! ### Expurgation -/

/-- **Expurgation.** Let `f ≥ 0` and let `c` be a codebook with `2 K` codewords, `K > 0`.  Then
one can keep `K` of them (the order embedding `φ` selects which) so that in the smaller codebook
`c ∘ φ` every off-diagonal row sum is at most `offSum f c / K`: at most `K` rows of the original
codebook can exceed twice the average row sum `offSum f c / (2 K)`, and deleting codewords only
decreases the remaining row sums. -/
theorem exists_subcodebook_rows_le {f : ι → ι → ℝ} (hf0 : ∀ x x', 0 ≤ f x x') {K : ℕ}
    (hK : 0 < K) (c : Fin (2 * K) → ι) :
    ∃ φ : Fin K ↪o Fin (2 * K), ∀ j,
      ∑ j', (if j = j' then 0 else f (c (φ j)) (c (φ j'))) ≤ offSum f c / K := by
  classical
  set r : Fin (2 * K) → ℝ := fun m => ∑ m', if m = m' then 0 else f (c m) (c m') with hr
  have hr0 : ∀ m, 0 ≤ r m := offRow_nonneg hf0 c
  set S := offSum f c with hS
  have hSr : S = ∑ m, r m := rfl
  have hS0 : 0 ≤ S := by rw [hSr]; exact Finset.sum_nonneg fun m _ => hr0 m
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  -- the good rows: at most the threshold `S / K`
  set G := univ.filter fun m => r m ≤ S / K with hG
  -- at most `K` rows are bad (Markov's inequality)
  have hbad : (univ.filter fun m => ¬ r m ≤ S / K).card ≤ K := by
    by_contra hlt
    rw [not_le] at hlt
    set Bd := univ.filter fun m => ¬ r m ≤ S / K
    have hne : Bd.Nonempty := Finset.card_pos.mp (by omega)
    have h1 : ∑ m ∈ Bd, r m ≤ S := by
      rw [hSr]
      exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun m _ _ => hr0 m
    have h2 : ∑ m ∈ Bd, S / K < ∑ m ∈ Bd, r m :=
      Finset.sum_lt_sum_of_nonempty hne fun m hm => by
        simpa using (Finset.mem_filter.mp hm).2
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : ((K : ℝ) + 1) ≤ Bd.card := by exact_mod_cast hlt
    have h4 : ((K : ℝ) + 1) * (S / K) ≤ Bd.card * (S / K) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have h5 : ((K : ℝ) + 1) * (S / K) = S + S / K := by field_simp
    have h6 : 0 ≤ S / K := by positivity
    linarith
  have hGcard : K ≤ G.card := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * K))))
      (fun m => r m ≤ S / K)
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [hG]; omega
  -- keep `K` good rows
  obtain ⟨T, hTG, hT⟩ := Finset.exists_subset_card_eq hGcard
  refine ⟨T.orderEmbOfFin hT, fun j => ?_⟩
  set φ := T.orderEmbOfFin hT
  have hsub : ∑ j', (if j = j' then 0 else f (c (φ j)) (c (φ j'))) ≤ r (φ j) := by
    have : ∑ j', (if j = j' then 0 else f (c (φ j)) (c (φ j'))) =
        ∑ m' ∈ univ.map φ.toEmbedding, (if φ j = m' then 0 else f (c (φ j)) (c m')) := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun j' _ => ?_
      simp [φ.injective.eq_iff]
    rw [this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun m' _ _ => by
      split_ifs; exacts [le_rfl, hf0 _ _]
  exact hsub.trans (Finset.mem_filter.mp (hTG (T.orderEmbOfFin_mem hT j))).2

/-- Expurgation, packaged: if for every `K` there is a codebook with `K` codewords and
off-diagonal sum at most `a K² β` (with `β ≥ 0` irrelevant here), then for every `K` there is a
codebook with `K` codewords all of whose off-diagonal row sums are at most `4 a K β`. -/
theorem exists_codebook_rows_le_of_offSum_le {f : ι → ι → ℝ} (hf0 : ∀ x x', 0 ≤ f x x')
    {a β : ℝ} (h : ∀ K : ℕ, ∃ c : Fin K → ι, offSum f c ≤ a * (K : ℝ) ^ 2 * β) (K : ℕ) :
    ∃ c : Fin K → ι, ∀ m,
      ∑ m', (if m = m' then 0 else f (c m) (c m')) ≤ 4 * a * K * β := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact ⟨Fin.elim0, fun m => m.elim0⟩
  obtain ⟨c, hc⟩ := h (2 * K)
  obtain ⟨φ, hφ⟩ := exists_subcodebook_rows_le hf0 hK c
  refine ⟨c ∘ φ, fun j => (hφ j).trans ?_⟩
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_iff₀ hKr]
  calc offSum f c ≤ a * ((2 * K : ℕ) : ℝ) ^ 2 * β := hc
    _ = 4 * a * K * β * K := by push_cast; ring

/-! ### Greedy choice -/

section Greedy

variable [Fintype ι] [Nonempty ι] {f : ι → ι → ℝ}

/-- **Greedy codebook, symmetric weights.** For a symmetric nonnegative `f` on a nonempty finite
type with `N` elements whose row sums are at most `B`, for every `K` there are `K` codewords with
total off-diagonal sum at most `K² · B / N`.  (Add the codewords one at a time; the average over
all candidates of the cost of adding a candidate to `K` existing codewords is at most
`2 K B / N`.) -/
theorem exists_codebook_offSum_le_of_symm (hf0 : ∀ x x', 0 ≤ f x x')
    (hsymm : ∀ x x', f x x' = f x' x) {B : ℝ} (hB : ∀ x, ∑ x', f x x' ≤ B) (K : ℕ) :
    ∃ c : Fin K → ι, offSum f c ≤ (K : ℝ) ^ 2 * (B / Fintype.card ι) := by
  have hB0 : 0 ≤ B :=
    (Finset.sum_nonneg fun x' _ => hf0 (Classical.arbitrary ι) x').trans (hB _)
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hBn : 0 ≤ B / N := by positivity
  induction K with
  | zero => exact ⟨Fin.elim0, by simp [offSum]⟩
  | succ K ih =>
    obtain ⟨c, hc⟩ := ih
    have havg : ∑ x : ι, ∑ j, f x (c j) ≤ ∑ _x : ι, (K : ℝ) * (B / N) := by
      rw [Finset.sum_comm]
      have hcol : ∀ j, ∑ x : ι, f x (c j) ≤ B := fun j => by
        simp only [hsymm _ (c j)]; exact hB (c j)
      calc ∑ j, ∑ x : ι, f x (c j) ≤ ∑ _j : Fin K, B :=
            Finset.sum_le_sum fun j _ => hcol j
        _ = ∑ _x : ι, (K : ℝ) * (B / N) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← hN]
          field_simp
    obtain ⟨x, -, hx⟩ := Finset.exists_le_of_sum_le univ_nonempty havg
    refine ⟨Fin.cons x c, ?_⟩
    have hrow : ∑ j, f (c j) x = ∑ j, f x (c j) :=
      Finset.sum_congr rfl fun j _ => hsymm _ _
    rw [offSum_cons, hrow]
    push_cast
    nlinarith

/-- **Greedy codebook, general weights.** For a nonnegative, not necessarily symmetric, `f` on a
nonempty finite type with `N` elements whose row sums are at most `B`, for every `K` there are
`K` codewords, each with column sum `∑ x, f x (c j) ≤ 2 B`, with total off-diagonal sum at most
`3 K² · B / N`.  (At least half of the candidates have column sum at most `2 B`; choose greedily
among those.) -/
theorem exists_codebook_offSum_le (hf0 : ∀ x x', 0 ≤ f x x') {B : ℝ}
    (hB : ∀ x, ∑ x', f x x' ≤ B) (K : ℕ) :
    ∃ c : Fin K → ι, (∀ j, ∑ x, f x (c j) ≤ 2 * B) ∧
      offSum f c ≤ 3 * (K : ℝ) ^ 2 * (B / Fintype.card ι) := by
  classical
  have hB0 : 0 ≤ B :=
    (Finset.sum_nonneg fun x' _ => hf0 (Classical.arbitrary ι) x').trans (hB _)
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hBn : 0 ≤ B / N := by positivity
  set G := univ.filter fun x : ι => ∑ x', f x' x ≤ 2 * B with hG
  set Bd := univ.filter fun x : ι => ¬ ∑ x', f x' x ≤ 2 * B with hBd
  have htot : ∑ x, ∑ x', f x' x ≤ N * B := by
    rw [Finset.sum_comm]
    calc ∑ x', ∑ x, f x' x ≤ ∑ _x' : ι, B := Finset.sum_le_sum fun x' _ => hB x'
      _ = N * B := by simp [hN]
  have hbad : 2 * (Bd.card : ℝ) ≤ N := by
    by_contra hlt
    rw [not_le] at hlt
    have hne : Bd.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < Bd.card := by linarith
      exact_mod_cast this
    have h1 : ∑ x ∈ Bd, ∑ x', f x' x ≤ N * B :=
      (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
        Finset.sum_nonneg fun x' _ => hf0 x' x).trans htot
    have h2 : ∑ _x ∈ Bd, 2 * B < ∑ x ∈ Bd, ∑ x', f x' x :=
      Finset.sum_lt_sum_of_nonempty hne fun x hx => by
        simpa using (Finset.mem_filter.mp hx).2
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    nlinarith
  have hGcard : N ≤ 2 * (G.card : ℝ) := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset ι))
      (fun x : ι => ∑ x', f x' x ≤ 2 * B)
    rw [Finset.card_univ] at this
    have h' : (G.card : ℝ) + Bd.card = N := by rw [hN, ← this]; push_cast; rfl
    linarith
  have hGne : G.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < G.card := by linarith
    exact_mod_cast this
  induction K with
  | zero => exact ⟨Fin.elim0, fun j => j.elim0, by simp [offSum]⟩
  | succ K ih =>
    obtain ⟨c, hcol, hc⟩ := ih
    have h1 : ∑ x ∈ G, ∑ j, f x (c j) ≤ K * (2 * B) := by
      rw [Finset.sum_comm]
      calc ∑ j, ∑ x ∈ G, f x (c j) ≤ ∑ j : Fin K, 2 * B :=
            Finset.sum_le_sum fun j _ =>
              (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
                hf0 x (c j)).trans (hcol j)
        _ = K * (2 * B) := by simp
    have h2 : ∑ x ∈ G, ∑ j, f (c j) x ≤ K * B := by
      rw [Finset.sum_comm]
      calc ∑ j, ∑ x ∈ G, f (c j) x ≤ ∑ j : Fin K, B :=
            Finset.sum_le_sum fun j _ =>
              (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
                hf0 (c j) x).trans (hB (c j))
        _ = K * B := by simp
    have havg : ∑ x ∈ G, ((∑ j, f x (c j)) + ∑ j, f (c j) x) ≤
        ∑ _x ∈ G, 6 * (K : ℝ) * (B / N) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have : N * (3 * (K : ℝ) * (B / N)) = 3 * K * B := by field_simp
      have h3 : N * (3 * (K : ℝ) * (B / N)) ≤ 2 * (G.card : ℝ) * (3 * (K : ℝ) * (B / N)) :=
        mul_le_mul_of_nonneg_right hGcard (by positivity)
      nlinarith
    obtain ⟨x, hxG, hx⟩ := Finset.exists_le_of_sum_le hGne havg
    refine ⟨Fin.cons x c, fun j => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa using (Finset.mem_filter.mp hxG).2
      · simpa using hcol j
    · rw [offSum_cons]
      push_cast
      nlinarith

/-! ### Greedy choice followed by expurgation -/

/-- **Greedy choice with expurgation, symmetric weights.** For a symmetric nonnegative `f` on a
nonempty finite type with `N` elements whose row sums are at most `B`, for every `K` there are
`K` codewords all of whose off-diagonal row sums are at most `4 K B / N`. -/
theorem exists_codebook_rows_le_of_symm (hf0 : ∀ x x', 0 ≤ f x x')
    (hsymm : ∀ x x', f x x' = f x' x) {B : ℝ} (hB : ∀ x, ∑ x', f x x' ≤ B) (K : ℕ) :
    ∃ c : Fin K → ι, ∀ m,
      ∑ m', (if m = m' then 0 else f (c m) (c m')) ≤ 4 * K * (B / Fintype.card ι) := by
  have h := exists_codebook_rows_le_of_offSum_le (a := 1) (β := B / Fintype.card ι) hf0
    (fun K => by simpa using exists_codebook_offSum_le_of_symm hf0 hsymm hB K) K
  simpa using h

/-- **Greedy choice with expurgation, without symmetry.** For a nonnegative `f` on a nonempty
finite type whose row sums are at most `B`, for every `K` there are `K` codewords all of whose
off-diagonal row sums are at most `12 K B / N`, where `N` is the number of candidates. -/
theorem exists_codebook_rows_le' (hf0 : ∀ x x', 0 ≤ f x x') {B : ℝ}
    (hB : ∀ x, ∑ x', f x x' ≤ B) (K : ℕ) :
    ∃ c : Fin K → ι, ∀ m,
      ∑ m', (if m = m' then 0 else f (c m) (c m')) ≤ 12 * K * (B / Fintype.card ι) := by
  obtain ⟨c, hc⟩ := exists_codebook_rows_le_of_offSum_le (a := 3) (β := B / Fintype.card ι) hf0
    (fun K => (exists_codebook_offSum_le hf0 hB K).imp fun _ h => h.2) K
  exact ⟨c, fun m => (hc m).trans_eq (by ring)⟩

end Greedy

end Applied.InformationTheory
