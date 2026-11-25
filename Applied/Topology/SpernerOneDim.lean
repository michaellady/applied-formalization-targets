import Mathlib

/-!
# Sperner's lemma in dimension one

Subdivide a segment into `n` small segments with vertices `0, 1, …, n`, and label each vertex
by a Boolean (two colours). If the two endpoints get different labels, then the number of small
segments whose two endpoints get different labels ("fully labelled" segments) is odd
(`sperner_one_dim`); in particular at least one exists (`sperner_one_dim_exists`).
-/

namespace Applied.Topology

open Finset

/-- Parity count: the number of label changes along `0, …, n` is even iff the endpoint labels
agree. -/
theorem card_label_changes_mod_two (L : ℕ → Bool) (n : ℕ) :
    ((range n).filter (fun i => L i ≠ L (i + 1))).card % 2 =
      if L 0 = L n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_add_one, filter_insert]
    have hn : n ∉ (range n).filter (fun i => L i ≠ L (i + 1)) := by simp
    by_cases h : L n ≠ L (n + 1)
    · rw [ite_eq_left h, card_insert_of_notMem hn]
      cases h0 : L 0 <;> cases h1 : L n <;> cases h2 : L (n + 1) <;>
        simp_all <;> omega
    · rw [ite_eq_right h]
      have h' : L n = L (n + 1) := by simpa using h
      rw [ih, h']

/-- One-dimensional Sperner lemma: if the endpoint labels differ, the number of fully labelled
small segments is odd. -/
theorem sperner_one_dim (L : ℕ → Bool) (n : ℕ) (h : L 0 ≠ L n) :
    Odd ((range n).filter (fun i => L i ≠ L (i + 1))).card := by
  have := card_label_changes_mod_two L n
  rw [ite_eq_right h] at this
  exact Nat.odd_iff.2 this

/-- In particular, some small segment `[i, i+1]`, `i < n`, is fully labelled. -/
theorem sperner_one_dim_exists (L : ℕ → Bool) (n : ℕ) (h : L 0 ≠ L n) :
    ∃ i < n, L i ≠ L (i + 1) := by
  obtain ⟨i, hi⟩ := Finset.card_pos.1 (sperner_one_dim L n h).pos
  simp only [mem_filter, mem_range] at hi
  exact ⟨i, hi.1, hi.2⟩

end Applied.Topology
