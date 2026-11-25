import Applied.Coding.Trifference

/-!
# Perfect `k`-hash codes and the elementary recursion bound

A code `C ⊆ {0, …, k-1}ⁿ` is a *perfect `k`-hash code* if every `k` distinct codewords take `k`
pairwise different values in some coordinate (the setting of Fredman–Komlós). For `k = 3` these
are the trifferent codes.

* `IsPerfectHashCode k C`: the definition.
* `isPerfectHashCode_three_iff`: for `k = 3` it is `IsTrifferent`.
* `IsPerfectHashCode.exists_shorter`: for `k ≥ 2` and a perfect `k`-hash code `C` of length
  `n + 1`, either `(k - 1) |C| ≤ k (k - 1)` (so `|C| ≤ k`) or there is a perfect `k`-hash code
  `C'` of length `n` with `(k - 1) |C| ≤ k |C'|`.
* `IsPerfectHashCode.card_le`: the elementary bound `|C| ≤ (k - 1) (k / (k - 1))ⁿ` for `k ≥ 2`
  (for `k = 3` this is Körner's bound `2 (3/2)ⁿ`).
-/

open Finset

namespace Applied.Coding

/-- Every `k` distinct codewords are separated (pairwise distinct values) by some coordinate. -/
def IsPerfectHashCode (k : ℕ) {n : ℕ} (C : Finset (Fin n → Fin k)) : Prop :=
  ∀ S ⊆ C, S.card = k → ∃ i, Set.InjOn (fun x => x i) (S : Set (Fin n → Fin k))

/-- For `k = 3`, perfect hash codes are exactly the trifferent codes. -/
theorem isPerfectHashCode_three_iff {n : ℕ} (C : Finset (Fin n → Fin 3)) :
    IsPerfectHashCode 3 C ↔ IsTrifferent C := by
  classical
  constructor
  · intro h x hx y hy z hz hxy hyz hxz
    have hS : ({x, y, z} : Finset (Fin n → Fin 3)) ⊆ C := by
      intro w hw; simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    obtain ⟨i, hi⟩ := h _ hS (card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩)
    refine ⟨i, fun e => hxy (hi (by simp) (by simp) e), fun e => hyz (hi (by simp) (by simp) e),
      fun e => hxz (hi (by simp) (by simp) e)⟩
  · intro h S hSC hS
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hS
    obtain ⟨i, h1, h2, h3⟩ := h x (hSC (by simp)) y (hSC (by simp)) z (hSC (by simp)) hxy hyz hxz
    refine ⟨i, ?_⟩
    intro a ha b hb e
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp_all [eq_comm])

/-- Some symbol appears in the first coordinate of at most a `1/k` fraction of the codewords. -/
private lemma exists_rare_symbol_k {k n : ℕ} (hk : 1 ≤ k) (C : Finset (Fin (n + 1) → Fin k)) :
    ∃ s : Fin k, k * (C.filter fun x => x 0 = s).card ≤ C.card := by
  classical
  have hsum : C.card = ∑ s : Fin k, (C.filter fun x => x 0 = s).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => mem_univ (x 0)
  by_contra hcon
  push Not at hcon
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, mem_univ _⟩
  have hlt : ∑ _s : Fin k, C.card < ∑ s : Fin k, k * (C.filter fun x => x 0 = s).card :=
    sum_lt_sum_of_nonempty hne fun s _ => hcon s
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← mul_sum, ← hsum] at hlt
  exact lt_irrefl _ hlt

/-- A set of words whose first symbols all avoid `s` cannot be separated by the first
coordinate once it has `k` elements. -/
private lemma not_injOn_zero {k n : ℕ} {S : Finset (Fin (n + 1) → Fin k)} {s : Fin k}
    (hS : S.card = k) (hs : ∀ x ∈ S, x 0 ≠ s) :
    ¬ Set.InjOn (fun x => x 0) (S : Set (Fin (n + 1) → Fin k)) := by
  classical
  intro hinj
  have := card_le_card_of_injOn (fun x : Fin (n + 1) → Fin k => x 0) (t := univ.erase s)
    (fun x hx => mem_erase.mpr ⟨hs x hx, mem_univ _⟩) hinj
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact (s.elim0)
    · exact h
  omega

/-- **Shortening step** for perfect `k`-hash codes: drop the words whose first symbol is the
rarest one, then delete the first coordinate. -/
theorem IsPerfectHashCode.exists_shorter {k n : ℕ} (hk2 : 2 ≤ k)
    {C : Finset (Fin (n + 1) → Fin k)} (hC : IsPerfectHashCode k C) :
    (k - 1) * C.card ≤ k * (k - 1) ∨ ∃ C' : Finset (Fin n → Fin k),
      IsPerfectHashCode k C' ∧ (k - 1) * C.card ≤ k * C'.card := by
  classical
  have hk : 1 ≤ k := by omega
  obtain ⟨s, hs⟩ := exists_rare_symbol_k hk C
  set D := C.filter fun x => ¬ x 0 = s with hD
  have hcard : (C.filter fun x => x 0 = s).card + D.card = C.card :=
    Finset.card_filter_add_card_filter_not (s := C) fun x => x 0 = s
  have hDC : D ⊆ C := Finset.filter_subset _ _
  have hDs : ∀ x ∈ D, x 0 ≠ s := fun x hx => (mem_filter.mp hx).2
  -- `(k - 1) |C| ≤ k |D|`
  have hkD : (k - 1) * C.card ≤ k * D.card := by
    have : k * C.card = k * (C.filter fun x => x 0 = s).card + k * D.card := by
      rw [← hcard, mul_add]
    have h2 : (k - 1) * C.card + C.card = k * C.card := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hk]
    omega
  rcases lt_or_ge D.card k with hsmall | hbig
  · left
    have : D.card ≤ k - 1 := by omega
    calc (k - 1) * C.card ≤ k * D.card := hkD
      _ ≤ k * (k - 1) := Nat.mul_le_mul_left _ this
  right
  -- deleting the first coordinate is injective on `D`
  have hinj : Set.InjOn (Fin.tail : (Fin (n + 1) → Fin k) → Fin n → Fin k) D := by
    intro x hx y hy hxy
    by_contra hne
    have hsub : ({x, y} : Finset _) ⊆ D := by
      intro w hw; simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl <;> assumption
    have hle : ({x, y} : Finset (Fin (n + 1) → Fin k)).card ≤ k := by
      rw [card_pair hne]; omega
    obtain ⟨S, hxyS, hSD, hScard⟩ := exists_subsuperset_card_eq hsub hle hbig
    obtain ⟨i, hi⟩ := hC S (hSD.trans hDC) hScard
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact not_injOn_zero hScard (fun z hz => hDs z (hSD hz)) hi
    · exact hne (hi (hxyS (by simp)) (hxyS (by simp)) (congrFun hxy j))
  refine ⟨D.image Fin.tail, ?_, ?_⟩
  · intro S' hS' hS'card
    set S := D.filter fun x : Fin (n + 1) → Fin k => (Fin.tail x : Fin n → Fin k) ∈ S' with hSdef
    have hSD : S ⊆ D := filter_subset _ _
    have himg : S.image Fin.tail = S' := by
      ext a
      simp only [mem_image, hSdef, mem_filter]
      constructor
      · rintro ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
      · intro ha
        obtain ⟨x, hx, rfl⟩ := mem_image.mp (hS' ha)
        exact ⟨x, ⟨hx, ha⟩, rfl⟩
    have hScard : S.card = k := by
      have := card_image_of_injOn (hinj.mono (by simpa using hSD))
      rw [himg] at this
      omega
    obtain ⟨i, hi⟩ := hC S (hSD.trans hDC) hScard
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact absurd hi (not_injOn_zero hScard fun z hz => hDs z (hSD hz))
    · refine ⟨j, ?_⟩
      intro a ha b hb e
      rw [← himg] at ha hb
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
      rw [hi hx hy e]
  · rw [card_image_of_injOn hinj]; exact hkD

/-- **Elementary bound for perfect `k`-hash codes** (`k ≥ 2`): `|C| ≤ (k - 1) (k / (k - 1))ⁿ`.
For `k = 3` this is Körner's bound `2 (3/2)ⁿ`. -/
theorem IsPerfectHashCode.card_le {k : ℕ} (hk : 2 ≤ k) : ∀ {n : ℕ}
    {C : Finset (Fin n → Fin k)}, IsPerfectHashCode k C →
    (C.card : ℝ) ≤ (k - 1) * ((k : ℝ) / (k - 1)) ^ n
  | 0, C, _ => by
    have h1 : C.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x _ y _
      exact Subsingleton.elim x y
    have : (C.card : ℝ) ≤ 1 := by exact_mod_cast h1
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    simp; linarith
  | n + 1, C, hC => by
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have hq : (1 : ℝ) ≤ (k : ℝ) / (k - 1) := by
      rw [le_div_iff₀ hk1]; linarith
    have hpow : (1 : ℝ) ≤ ((k : ℝ) / (k - 1)) ^ n := one_le_pow₀ hq
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have key : ∀ m : ℝ, ((k : ℝ) - 1) * C.card ≤ k * m →
        m ≤ (k - 1) * ((k : ℝ) / (k - 1)) ^ n →
        (C.card : ℝ) ≤ (k - 1) * ((k : ℝ) / (k - 1)) ^ (n + 1) := by
      intro m h1 h2
      rw [pow_succ]
      have e : (k - 1) * (((k : ℝ) / (k - 1)) ^ n * ((k : ℝ) / (k - 1)))
          = (k - 1) * ((k : ℝ) / (k - 1)) ^ n * k / (k - 1) := by
        field_simp
      rw [e, le_div_iff₀ hk1]
      nlinarith
    rcases hC.exists_shorter hk with hsmall | ⟨C', hC', hle⟩
    · have h : ((k : ℝ) - 1) * C.card ≤ k * (k - 1) := by
        rw [← hcast]; exact_mod_cast hsmall
      refine key (k - 1) h ?_
      nlinarith
    · have h : ((k : ℝ) - 1) * C.card ≤ k * C'.card := by
        rw [← hcast]; exact_mod_cast hle
      exact key _ h (IsPerfectHashCode.card_le hk hC')

end Applied.Coding
